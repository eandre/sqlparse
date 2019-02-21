// Copyright 2015 The Cockroach Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied. See the License for the specific language governing
// permissions and limitations under the License.

package tree

import (
	"context"
	"fmt"
	"math"
	"math/big"
	"regexp"
	"strconv"
	"strings"
	"time"
	"unicode/utf8"

	"github.com/pkg/errors"

	apd "github.com/cockroachdb/apd/v2"
	"github.com/eandre/sqlparse/coltypes"
	"github.com/eandre/sqlparse/lex"
	"github.com/eandre/sqlparse/pkg/util/bitarray"
	"github.com/eandre/sqlparse/pkg/util/duration"
	"github.com/eandre/sqlparse/pkg/util/hlc"
	"github.com/eandre/sqlparse/pkg/util/json"
	"github.com/eandre/sqlparse/pkg/util/pgerror"
	"github.com/eandre/sqlparse/pkg/util/timeofday"
	"github.com/eandre/sqlparse/pkg/util/timeutil"
	"github.com/eandre/sqlparse/sem/types"
	"github.com/eandre/sqlparse/sessiondata"
)

var (
	errIntOutOfRange   = pgerror.NewError(pgerror.CodeNumericValueOutOfRangeError, "integer out of range")
	errFloatOutOfRange = pgerror.NewError(pgerror.CodeNumericValueOutOfRangeError, "float out of range")
	errDecOutOfRange   = pgerror.NewError(pgerror.CodeNumericValueOutOfRangeError, "decimal out of range")

	// ErrDivByZero is reported on a division by zero.
	ErrDivByZero = pgerror.NewError(pgerror.CodeDivisionByZeroError, "division by zero")
	// ErrZeroModulus is reported when computing the rest of a division by zero.
	ErrZeroModulus = pgerror.NewError(pgerror.CodeDivisionByZeroError, "zero modulus")

	big10E6  = big.NewInt(1e6)
	big10E10 = big.NewInt(1e10)
)

// SecondsInDay is the number of seconds in a Day.
const SecondsInDay = 24 * 60 * 60

// UnaryOp is a unary operator.
type UnaryOp struct {
	Typ        types.T
	ReturnType types.T

	types   TypeList
	retType ReturnTyper
}

func (op *UnaryOp) params() TypeList {
	return op.types
}

func (op *UnaryOp) returnType() ReturnTyper {
	return op.retType
}

func (*UnaryOp) preferred() bool {
	return false
}

func init() {
	for op, overload := range UnaryOps {
		for i, impl := range overload {
			casted := impl.(*UnaryOp)
			casted.types = ArgTypes{{"arg", casted.Typ}}
			casted.retType = FixedReturnType(casted.ReturnType)
			UnaryOps[op][i] = casted
		}
	}
}

// unaryOpOverload is an overloaded set of unary operator implementations.
type unaryOpOverload []overloadImpl

// UnaryOps contains the unary operations indexed by operation type.
var UnaryOps = map[UnaryOperator]unaryOpOverload{
	UnaryMinus: {
		&UnaryOp{
			Typ:        types.Int,
			ReturnType: types.Int,
		},
		&UnaryOp{
			Typ:        types.Float,
			ReturnType: types.Float,
		},
		&UnaryOp{
			Typ:        types.Decimal,
			ReturnType: types.Decimal,
		},
		&UnaryOp{
			Typ:        types.Interval,
			ReturnType: types.Interval,
		},
	},

	UnaryComplement: {
		&UnaryOp{
			Typ:        types.Int,
			ReturnType: types.Int,
		},
		&UnaryOp{
			Typ:        types.BitArray,
			ReturnType: types.BitArray,
		},
		&UnaryOp{
			Typ:        types.INet,
			ReturnType: types.INet,
		},
	},
}

// BinOp is a binary operator.
type BinOp struct {
	LeftType     types.T
	RightType    types.T
	ReturnType   types.T
	NullableArgs bool

	types   TypeList
	retType ReturnTyper
}

func (op *BinOp) params() TypeList {
	return op.types
}

func (op *BinOp) matchParams(l, r types.T) bool {
	return op.params().MatchAt(l, 0) && op.params().MatchAt(r, 1)
}

func (op *BinOp) returnType() ReturnTyper {
	return op.retType
}

func (*BinOp) preferred() bool {
	return false
}

// AppendToMaybeNullArray appends an element to an array. If the first
// argument is NULL, an array of one element is created.
func AppendToMaybeNullArray(typ types.T, left Datum, right Datum) (Datum, error) {
	result := NewDArray(typ)
	if left != DNull {
		for _, e := range MustBeDArray(left).Array {
			if err := result.Append(e); err != nil {
				return nil, err
			}
		}
	}
	if err := result.Append(right); err != nil {
		return nil, err
	}
	return result, nil
}

// PrependToMaybeNullArray prepends an element in the front of an arrray.
// If the argument is NULL, an array of one element is created.
func PrependToMaybeNullArray(typ types.T, left Datum, right Datum) (Datum, error) {
	result := NewDArray(typ)
	if err := result.Append(left); err != nil {
		return nil, err
	}
	if right != DNull {
		for _, e := range MustBeDArray(right).Array {
			if err := result.Append(e); err != nil {
				return nil, err
			}
		}
	}
	return result, nil
}

// TODO(justin): these might be improved by making arrays into an interface and
// then introducing a ConcatenatedArray implementation which just references two
// existing arrays. This would optimize the common case of appending an element
// (or array) to an array from O(n) to O(1).
func initArrayElementConcatenation() {
	for _, t := range types.AnyNonArray {
		typ := t
		BinOps[Concat] = append(BinOps[Concat], &BinOp{
			LeftType:     types.TArray{Typ: typ},
			RightType:    typ,
			ReturnType:   types.TArray{Typ: typ},
			NullableArgs: true,
		})

		BinOps[Concat] = append(BinOps[Concat], &BinOp{
			LeftType:     typ,
			RightType:    types.TArray{Typ: typ},
			ReturnType:   types.TArray{Typ: typ},
			NullableArgs: true,
		})
	}
}

// ConcatArrays concatenates two arrays.
func ConcatArrays(typ types.T, left Datum, right Datum) (Datum, error) {
	if left == DNull && right == DNull {
		return DNull, nil
	}
	result := NewDArray(typ)
	if left != DNull {
		for _, e := range MustBeDArray(left).Array {
			if err := result.Append(e); err != nil {
				return nil, err
			}
		}
	}
	if right != DNull {
		for _, e := range MustBeDArray(right).Array {
			if err := result.Append(e); err != nil {
				return nil, err
			}
		}
	}
	return result, nil
}

func initArrayToArrayConcatenation() {
	for _, t := range types.AnyNonArray {
		typ := t
		BinOps[Concat] = append(BinOps[Concat], &BinOp{
			LeftType:     types.TArray{Typ: typ},
			RightType:    types.TArray{Typ: typ},
			ReturnType:   types.TArray{Typ: typ},
			NullableArgs: true,
		})
	}
}

func init() {
	initArrayElementConcatenation()
	initArrayToArrayConcatenation()
}

func init() {
	for op, overload := range BinOps {
		for i, impl := range overload {
			casted := impl.(*BinOp)
			casted.types = ArgTypes{{"left", casted.LeftType}, {"right", casted.RightType}}
			casted.retType = FixedReturnType(casted.ReturnType)
			BinOps[op][i] = casted
		}
	}
}

// binOpOverload is an overloaded set of binary operator implementations.
type binOpOverload []overloadImpl

func (o binOpOverload) lookupImpl(left, right types.T) (*BinOp, bool) {
	for _, fn := range o {
		casted := fn.(*BinOp)
		if casted.matchParams(left, right) {
			return casted, true
		}
	}
	return nil, false
}

// getJSONPath is used for the #> and #>> operators.
func getJSONPath(j DJSON, ary DArray) (Datum, error) {
	// TODO(justin): this is slightly annoying because we have to allocate
	// a new array since the JSON package isn't aware of DArray.
	path := make([]string, len(ary.Array))
	for i, v := range ary.Array {
		if v == DNull {
			return DNull, nil
		}
		path[i] = string(MustBeDString(v))
	}
	result, err := json.FetchPath(j.JSON, path)
	if err != nil {
		return nil, err
	}
	if result == nil {
		return DNull, nil
	}
	return &DJSON{result}, nil
}

func newCannotMixBitArraySizesError(op string) error {
	return pgerror.NewErrorf(pgerror.CodeStringDataLengthMismatchError,
		"cannot %s bit strings of different sizes", op)
}

// BinOps contains the binary operations indexed by operation type.
var BinOps = map[BinaryOperator]binOpOverload{
	Bitand: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.BitArray,
			RightType:  types.BitArray,
			ReturnType: types.BitArray,
		},
		&BinOp{
			LeftType:   types.INet,
			RightType:  types.INet,
			ReturnType: types.INet,
		},
	},

	Bitor: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.BitArray,
			RightType:  types.BitArray,
			ReturnType: types.BitArray,
		},
		&BinOp{
			LeftType:   types.INet,
			RightType:  types.INet,
			ReturnType: types.INet,
		},
	},

	Bitxor: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.BitArray,
			RightType:  types.BitArray,
			ReturnType: types.BitArray,
		},
	},

	Plus: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Int,
			ReturnType: types.Date,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Date,
			ReturnType: types.Date,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Time,
			ReturnType: types.Timestamp,
		},
		&BinOp{
			LeftType:   types.Time,
			RightType:  types.Date,
			ReturnType: types.Timestamp,
		},
		&BinOp{
			LeftType:   types.Time,
			RightType:  types.Interval,
			ReturnType: types.Time,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Time,
			ReturnType: types.Time,
		},
		&BinOp{
			LeftType:   types.Timestamp,
			RightType:  types.Interval,
			ReturnType: types.Timestamp,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Timestamp,
			ReturnType: types.Timestamp,
		},
		&BinOp{
			LeftType:   types.TimestampTZ,
			RightType:  types.Interval,
			ReturnType: types.TimestampTZ,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.TimestampTZ,
			ReturnType: types.TimestampTZ,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Interval,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Interval,
			ReturnType: types.TimestampTZ,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Date,
			ReturnType: types.TimestampTZ,
		},
		&BinOp{
			LeftType:   types.INet,
			RightType:  types.Int,
			ReturnType: types.INet,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.INet,
			ReturnType: types.INet,
		},
	},

	Minus: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Int,
			ReturnType: types.Date,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Date,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Time,
			ReturnType: types.Timestamp,
		},
		&BinOp{
			LeftType:   types.Time,
			RightType:  types.Time,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Timestamp,
			RightType:  types.Timestamp,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.TimestampTZ,
			RightType:  types.TimestampTZ,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Timestamp,
			RightType:  types.TimestampTZ,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.TimestampTZ,
			RightType:  types.Timestamp,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Time,
			RightType:  types.Interval,
			ReturnType: types.Time,
		},
		&BinOp{
			LeftType:   types.Timestamp,
			RightType:  types.Interval,
			ReturnType: types.Timestamp,
		},
		&BinOp{
			LeftType:   types.TimestampTZ,
			RightType:  types.Interval,
			ReturnType: types.TimestampTZ,
		},
		&BinOp{
			LeftType:   types.Date,
			RightType:  types.Interval,
			ReturnType: types.TimestampTZ,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Interval,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.String,
			ReturnType: types.JSON,
		},
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.Int,
			ReturnType: types.JSON,
		},
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.TArray{Typ: types.String},
			ReturnType: types.JSON,
		},
		&BinOp{
			LeftType:   types.INet,
			RightType:  types.INet,
			ReturnType: types.Int,
		},
		&BinOp{
			// Note: postgres ver 10 does NOT have Int - INet. Throws ERROR: 42883.
			LeftType:   types.INet,
			RightType:  types.Int,
			ReturnType: types.INet,
		},
	},

	Mult: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		// The following two overloads are needed because DInt/DInt = DDecimal. Due
		// to this operation, normalization may sometimes create a DInt * DDecimal
		// operation.
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Interval,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Int,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Float,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Interval,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Interval,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Decimal,
			ReturnType: types.Interval,
		},
	},

	Div: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Int,
			ReturnType: types.Interval,
		},
		&BinOp{
			LeftType:   types.Interval,
			RightType:  types.Float,
			ReturnType: types.Interval,
		},
	},

	FloorDiv: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
	},

	Mod: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
	},

	Concat: {
		&BinOp{
			LeftType:   types.String,
			RightType:  types.String,
			ReturnType: types.String,
		},
		&BinOp{
			LeftType:   types.Bytes,
			RightType:  types.Bytes,
			ReturnType: types.Bytes,
		},
		&BinOp{
			LeftType:   types.BitArray,
			RightType:  types.BitArray,
			ReturnType: types.BitArray,
		},
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.JSON,
			ReturnType: types.JSON,
		},
	},

	// TODO(pmattis): Check that the shift is valid.
	LShift: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.BitArray,
			RightType:  types.Int,
			ReturnType: types.BitArray,
		},
		&BinOp{
			LeftType:   types.INet,
			RightType:  types.INet,
			ReturnType: types.Bool,
		},
	},

	RShift: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.BitArray,
			RightType:  types.Int,
			ReturnType: types.BitArray,
		},
		&BinOp{
			LeftType:   types.INet,
			RightType:  types.INet,
			ReturnType: types.Bool,
		},
	},

	Pow: {
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Int,
			ReturnType: types.Int,
		},
		&BinOp{
			LeftType:   types.Float,
			RightType:  types.Float,
			ReturnType: types.Float,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Decimal,
			RightType:  types.Int,
			ReturnType: types.Decimal,
		},
		&BinOp{
			LeftType:   types.Int,
			RightType:  types.Decimal,
			ReturnType: types.Decimal,
		},
	},

	JSONFetchVal: {
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.String,
			ReturnType: types.JSON,
		},
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.Int,
			ReturnType: types.JSON,
		},
	},

	JSONFetchValPath: {
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.TArray{Typ: types.String},
			ReturnType: types.JSON,
		},
	},

	JSONFetchText: {
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.String,
			ReturnType: types.String,
		},
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.Int,
			ReturnType: types.String,
		},
	},

	JSONFetchTextPath: {
		&BinOp{
			LeftType:   types.JSON,
			RightType:  types.TArray{Typ: types.String},
			ReturnType: types.String,
		},
	},
}

// timestampMinusBinOp is the implementation of the subtraction
// between types.TimestampTZ operands.
var timestampMinusBinOp *BinOp

func init() {
	timestampMinusBinOp, _ = BinOps[Minus].lookupImpl(types.TimestampTZ, types.TimestampTZ)
}

// CmpOp is a comparison operator.
type CmpOp struct {
	LeftType  types.T
	RightType types.T

	// If NullableArgs is false, the operator returns NULL
	// whenever either argument is NULL.
	NullableArgs bool

	types       TypeList
	isPreferred bool
}

func (op *CmpOp) params() TypeList {
	return op.types
}

func (op *CmpOp) matchParams(l, r types.T) bool {
	return op.params().MatchAt(l, 0) && op.params().MatchAt(r, 1)
}

var cmpOpReturnType = FixedReturnType(types.Bool)

func (op *CmpOp) returnType() ReturnTyper {
	return cmpOpReturnType
}

func (op *CmpOp) preferred() bool {
	return op.isPreferred
}

func init() {
	// Array equality comparisons.
	for _, t := range types.AnyNonArray {
		CmpOps[EQ] = append(CmpOps[EQ], &CmpOp{
			LeftType:  types.TArray{Typ: t},
			RightType: types.TArray{Typ: t},
		})

		CmpOps[IsNotDistinctFrom] = append(CmpOps[IsNotDistinctFrom], &CmpOp{
			LeftType:     types.TArray{Typ: t},
			RightType:    types.TArray{Typ: t},
			NullableArgs: true,
		})
	}
}

func init() {
	for op, overload := range CmpOps {
		for i, impl := range overload {
			casted := impl.(*CmpOp)
			casted.types = ArgTypes{{"left", casted.LeftType}, {"right", casted.RightType}}
			CmpOps[op][i] = casted
		}
	}
}

// cmpOpOverload is an overloaded set of comparison operator implementations.
type cmpOpOverload []overloadImpl

func (o cmpOpOverload) lookupImpl(left, right types.T) (*CmpOp, bool) {
	for _, fn := range o {
		casted := fn.(*CmpOp)
		if casted.matchParams(left, right) {
			return casted, true
		}
	}
	return nil, false
}

func makeCmpOpOverload(a, b types.T, nullableArgs bool) *CmpOp {
	return &CmpOp{
		LeftType:     a,
		RightType:    b,
		NullableArgs: nullableArgs,
	}
}

func makeEqFn(a, b types.T) *CmpOp {
	return makeCmpOpOverload(a, b, false /* NullableArgs */)
}
func makeLtFn(a, b types.T) *CmpOp {
	return makeCmpOpOverload(a, b, false /* NullableArgs */)
}
func makeLeFn(a, b types.T) *CmpOp {
	return makeCmpOpOverload(a, b, false /* NullableArgs */)
}
func makeIsFn(a, b types.T) *CmpOp {
	return makeCmpOpOverload(a, b, true /* NullableArgs */)
}

// CmpOps contains the comparison operations indexed by operation type.
var CmpOps = map[ComparisonOperator]cmpOpOverload{
	EQ: {
		// Single-type comparisons.
		makeEqFn(types.Bool, types.Bool),
		makeEqFn(types.Bytes, types.Bytes),
		makeEqFn(types.Date, types.Date),
		makeEqFn(types.Decimal, types.Decimal),
		makeEqFn(types.FamCollatedString, types.FamCollatedString),
		makeEqFn(types.Float, types.Float),
		makeEqFn(types.INet, types.INet),
		makeEqFn(types.Int, types.Int),
		makeEqFn(types.Interval, types.Interval),
		makeEqFn(types.JSON, types.JSON),
		makeEqFn(types.Oid, types.Oid),
		makeEqFn(types.String, types.String),
		makeEqFn(types.Time, types.Time),
		makeEqFn(types.Timestamp, types.Timestamp),
		makeEqFn(types.TimestampTZ, types.TimestampTZ),
		makeEqFn(types.UUID, types.UUID),
		makeEqFn(types.BitArray, types.BitArray),

		// Mixed-type comparisons.
		makeEqFn(types.Date, types.Timestamp),
		makeEqFn(types.Date, types.TimestampTZ),
		makeEqFn(types.Decimal, types.Float),
		makeEqFn(types.Decimal, types.Int),
		makeEqFn(types.Float, types.Decimal),
		makeEqFn(types.Float, types.Int),
		makeEqFn(types.Int, types.Decimal),
		makeEqFn(types.Int, types.Float),
		makeEqFn(types.Timestamp, types.Date),
		makeEqFn(types.Timestamp, types.TimestampTZ),
		makeEqFn(types.TimestampTZ, types.Date),
		makeEqFn(types.TimestampTZ, types.Timestamp),

		// Tuple comparison.
		&CmpOp{
			LeftType:  types.FamTuple,
			RightType: types.FamTuple,
		},
	},

	LT: {
		// Single-type comparisons.
		makeLtFn(types.Bool, types.Bool),
		makeLtFn(types.Bytes, types.Bytes),
		makeLtFn(types.Date, types.Date),
		makeLtFn(types.Decimal, types.Decimal),
		makeLtFn(types.FamCollatedString, types.FamCollatedString),
		makeLtFn(types.Float, types.Float),
		makeLtFn(types.INet, types.INet),
		makeLtFn(types.Int, types.Int),
		makeLtFn(types.Interval, types.Interval),
		makeLtFn(types.Oid, types.Oid),
		makeLtFn(types.String, types.String),
		makeLtFn(types.Time, types.Time),
		makeLtFn(types.Timestamp, types.Timestamp),
		makeLtFn(types.TimestampTZ, types.TimestampTZ),
		makeLtFn(types.UUID, types.UUID),
		makeLtFn(types.BitArray, types.BitArray),

		// Mixed-type comparisons.
		makeLtFn(types.Date, types.Timestamp),
		makeLtFn(types.Date, types.TimestampTZ),
		makeLtFn(types.Decimal, types.Float),
		makeLtFn(types.Decimal, types.Int),
		makeLtFn(types.Float, types.Decimal),
		makeLtFn(types.Float, types.Int),
		makeLtFn(types.Int, types.Decimal),
		makeLtFn(types.Int, types.Float),
		makeLtFn(types.Timestamp, types.Date),
		makeLtFn(types.Timestamp, types.TimestampTZ),
		makeLtFn(types.TimestampTZ, types.Date),
		makeLtFn(types.TimestampTZ, types.Timestamp),

		// Tuple comparison.
		&CmpOp{
			LeftType:  types.FamTuple,
			RightType: types.FamTuple,
		},
	},

	LE: {
		// Single-type comparisons.
		makeLeFn(types.Bool, types.Bool),
		makeLeFn(types.Bytes, types.Bytes),
		makeLeFn(types.Date, types.Date),
		makeLeFn(types.Decimal, types.Decimal),
		makeLeFn(types.FamCollatedString, types.FamCollatedString),
		makeLeFn(types.Float, types.Float),
		makeLeFn(types.INet, types.INet),
		makeLeFn(types.Int, types.Int),
		makeLeFn(types.Interval, types.Interval),
		makeLeFn(types.Oid, types.Oid),
		makeLeFn(types.String, types.String),
		makeLeFn(types.Time, types.Time),
		makeLeFn(types.Timestamp, types.Timestamp),
		makeLeFn(types.TimestampTZ, types.TimestampTZ),
		makeLeFn(types.UUID, types.UUID),
		makeLeFn(types.BitArray, types.BitArray),

		// Mixed-type comparisons.
		makeLeFn(types.Date, types.Timestamp),
		makeLeFn(types.Date, types.TimestampTZ),
		makeLeFn(types.Decimal, types.Float),
		makeLeFn(types.Decimal, types.Int),
		makeLeFn(types.Float, types.Decimal),
		makeLeFn(types.Float, types.Int),
		makeLeFn(types.Int, types.Decimal),
		makeLeFn(types.Int, types.Float),
		makeLeFn(types.Timestamp, types.Date),
		makeLeFn(types.Timestamp, types.TimestampTZ),
		makeLeFn(types.TimestampTZ, types.Date),
		makeLeFn(types.TimestampTZ, types.Timestamp),

		// Tuple comparison.
		&CmpOp{
			LeftType:  types.FamTuple,
			RightType: types.FamTuple,
		},
	},

	IsNotDistinctFrom: {
		&CmpOp{
			LeftType:     types.Unknown,
			RightType:    types.Unknown,
			NullableArgs: true,
			// Avoids ambiguous comparison error for NULL IS NOT DISTINCT FROM NULL>
			isPreferred: true,
		},
		// Single-type comparisons.
		makeIsFn(types.Bool, types.Bool),
		makeIsFn(types.Bytes, types.Bytes),
		makeIsFn(types.Date, types.Date),
		makeIsFn(types.Decimal, types.Decimal),
		makeIsFn(types.FamCollatedString, types.FamCollatedString),
		makeIsFn(types.Float, types.Float),
		makeIsFn(types.INet, types.INet),
		makeIsFn(types.Int, types.Int),
		makeIsFn(types.Interval, types.Interval),
		makeIsFn(types.JSON, types.JSON),
		makeIsFn(types.Oid, types.Oid),
		makeIsFn(types.String, types.String),
		makeIsFn(types.Time, types.Time),
		makeIsFn(types.Timestamp, types.Timestamp),
		makeIsFn(types.TimestampTZ, types.TimestampTZ),
		makeIsFn(types.UUID, types.UUID),
		makeIsFn(types.BitArray, types.BitArray),

		// Mixed-type comparisons.
		makeIsFn(types.Date, types.Timestamp),
		makeIsFn(types.Date, types.TimestampTZ),
		makeIsFn(types.Decimal, types.Float),
		makeIsFn(types.Decimal, types.Int),
		makeIsFn(types.Float, types.Decimal),
		makeIsFn(types.Float, types.Int),
		makeIsFn(types.Int, types.Decimal),
		makeIsFn(types.Int, types.Float),
		makeIsFn(types.Timestamp, types.Date),
		makeIsFn(types.Timestamp, types.TimestampTZ),
		makeIsFn(types.TimestampTZ, types.Date),
		makeIsFn(types.TimestampTZ, types.Timestamp),

		// Tuple comparison.
		&CmpOp{
			LeftType:     types.FamTuple,
			RightType:    types.FamTuple,
			NullableArgs: true,
		},
	},

	In: {
		makeEvalTupleIn(types.Bool),
		makeEvalTupleIn(types.Bytes),
		makeEvalTupleIn(types.Date),
		makeEvalTupleIn(types.Decimal),
		makeEvalTupleIn(types.FamCollatedString),
		makeEvalTupleIn(types.FamTuple),
		makeEvalTupleIn(types.Float),
		makeEvalTupleIn(types.INet),
		makeEvalTupleIn(types.Int),
		makeEvalTupleIn(types.Interval),
		makeEvalTupleIn(types.JSON),
		makeEvalTupleIn(types.Oid),
		makeEvalTupleIn(types.String),
		makeEvalTupleIn(types.Time),
		makeEvalTupleIn(types.Timestamp),
		makeEvalTupleIn(types.TimestampTZ),
		makeEvalTupleIn(types.UUID),
		makeEvalTupleIn(types.BitArray),
	},

	Like: {
		&CmpOp{
			LeftType:  types.String,
			RightType: types.String,
		},
	},

	ILike: {
		&CmpOp{
			LeftType:  types.String,
			RightType: types.String,
		},
	},

	SimilarTo: {
		&CmpOp{
			LeftType:  types.String,
			RightType: types.String,
		},
	},

	RegMatch: {
		&CmpOp{
			LeftType:  types.String,
			RightType: types.String,
		},
	},

	RegIMatch: {
		&CmpOp{
			LeftType:  types.String,
			RightType: types.String,
		},
	},

	JSONExists: {
		&CmpOp{
			LeftType:  types.JSON,
			RightType: types.String,
		},
	},

	JSONSomeExists: {
		&CmpOp{
			LeftType:  types.JSON,
			RightType: types.TArray{Typ: types.String},
		},
	},

	JSONAllExists: {
		&CmpOp{
			LeftType:  types.JSON,
			RightType: types.TArray{Typ: types.String},
		},
	},

	Contains: {
		&CmpOp{
			LeftType:  types.JSON,
			RightType: types.JSON,
		},
	},

	ContainedBy: {
		&CmpOp{
			LeftType:  types.JSON,
			RightType: types.JSON,
		},
	},
}

// This map contains the inverses for operators in the CmpOps map that have
// inverses.
var cmpOpsInverse map[ComparisonOperator]ComparisonOperator

func init() {
	cmpOpsInverse = make(map[ComparisonOperator]ComparisonOperator)
	for cmpOpIdx := range comparisonOpName {
		cmpOp := ComparisonOperator(cmpOpIdx)
		newOp, _, _, _, _ := foldComparisonExpr(cmpOp, DNull, DNull)
		if newOp != cmpOp {
			cmpOpsInverse[newOp] = cmpOp
			cmpOpsInverse[cmpOp] = newOp
		}
	}
}

func boolFromCmp(cmp int, op ComparisonOperator) *DBool {
	switch op {
	case EQ, IsNotDistinctFrom:
		return MakeDBool(cmp == 0)
	case LT:
		return MakeDBool(cmp < 0)
	case LE:
		return MakeDBool(cmp <= 0)
	default:
		panic(fmt.Sprintf("unexpected ComparisonOperator in boolFromCmp: %v", op))
	}
}

func makeEvalTupleIn(typ types.T) *CmpOp {
	return &CmpOp{
		LeftType:     typ,
		RightType:    types.FamTuple,
		NullableArgs: true,
	}
}

// MultipleResultsError is returned by QueryRow when more than one result is
// encountered.
type MultipleResultsError struct {
	SQL string // the query that produced this error
}

func (e *MultipleResultsError) Error() string {
	return fmt.Sprintf("%s: unexpected multiple results", e.SQL)
}

// EvalDatabase consists of functions that reference the session database
// and is to be used from EvalContext.
type EvalDatabase interface {
	// ParseQualifiedTableName parses a SQL string of the form
	// `[ database_name . ] [ schema_name . ] table_name`.
	ParseQualifiedTableName(ctx context.Context, sql string) (*TableName, error)

	// ResolveTableName expands the given table name and
	// makes it point to a valid object.
	// If the database name is not given, it uses the search path to find it, and
	// sets it on the returned TableName.
	// It returns an error if the table doesn't exist.
	ResolveTableName(ctx context.Context, tn *TableName) error

	// LookupSchema looks up the schema with the given name in the given
	// database.
	LookupSchema(ctx context.Context, dbName, scName string) (found bool, scMeta SchemaMeta, err error)
}

// EvalPlanner is a limited planner that can be used from EvalContext.
type EvalPlanner interface {
	EvalDatabase
	// ParseType parses a column type.
	ParseType(sql string) (coltypes.CastTargetType, error)

	// EvalSubquery returns the Datum for the given subquery node.
	EvalSubquery(expr *Subquery) (Datum, error)
}

// SequenceOperators is used for various sql related functions that can
// be used from EvalContext.
type SequenceOperators interface {
	EvalDatabase
	// IncrementSequence increments the given sequence and returns the result.
	// It returns an error if the given name is not a sequence.
	// The caller must ensure that seqName is fully qualified already.
	IncrementSequence(ctx context.Context, seqName *TableName) (int64, error)

	// GetLatestValueInSessionForSequence returns the value most recently obtained by
	// nextval() for the given sequence in this session.
	GetLatestValueInSessionForSequence(ctx context.Context, seqName *TableName) (int64, error)

	// SetSequenceValue sets the sequence's value.
	// If isCalled is false, the sequence is set such that the next time nextval() is called,
	// `newVal` is returned. Otherwise, the next call to nextval will return
	// `newVal + seqOpts.Increment`.
	SetSequenceValue(ctx context.Context, seqName *TableName, newVal int64, isCalled bool) error
}

// TimestampToDecimal converts the logical timestamp into a decimal
// value with the number of nanoseconds in the integer part and the
// logical counter in the decimal part.
func TimestampToDecimal(ts hlc.Timestamp) *DDecimal {
	// Compute Walltime * 10^10 + Logical.
	// We need 10 decimals for the Logical field because its maximum
	// value is 4294967295 (2^32-1), a value with 10 decimal digits.
	var res DDecimal
	val := &res.Coeff
	val.SetInt64(ts.WallTime)
	val.Mul(val, big10E10)
	val.Add(val, big.NewInt(int64(ts.Logical)))

	// Shift 10 decimals to the right, so that the logical
	// field appears as fractional part.
	res.Decimal.Exponent = -10
	return &res
}

// pgSignatureRegexp matches a Postgres function type signature, capturing the
// name of the function into group 1.
// e.g. function(a, b, c) or function( a )
var pgSignatureRegexp = regexp.MustCompile(`^\s*([\w\.]+)\s*\((?:(?:\s*\w+\s*,)*\s*\w+)?\s*\)\s*$`)

// regTypeInfo contains details on a pg_catalog table that has a reg* type.
type regTypeInfo struct {
	tableName string
	// nameCol is the name of the column that contains the table's entity name.
	nameCol string
	// objName is a human-readable name describing the objects in the table.
	objName string
	// errType is the pg error code in case the object does not exist.
	errType string
}

// regTypeInfos maps an coltypes.TOid to a regTypeInfo that describes the
// pg_catalog table that contains the entities of the type of the key.
var regTypeInfos = map[*coltypes.TOid]regTypeInfo{
	coltypes.RegClass:     {"pg_class", "relname", "relation", pgerror.CodeUndefinedTableError},
	coltypes.RegType:      {"pg_type", "typname", "type", pgerror.CodeUndefinedObjectError},
	coltypes.RegProc:      {"pg_proc", "proname", "function", pgerror.CodeUndefinedFunctionError},
	coltypes.RegProcedure: {"pg_proc", "proname", "function", pgerror.CodeUndefinedFunctionError},
	coltypes.RegNamespace: {"pg_namespace", "nspname", "namespace", pgerror.CodeUndefinedObjectError},
}

// ensureExpectedType will return an error if a datum does not match the
// provided type. If the expected type is Any or if the datum is a Null
// type, then no error will be returned.
func ensureExpectedType(exp types.T, d Datum) error {
	if !(exp.FamilyEqual(types.Any) || d.ResolvedType().Equivalent(types.Unknown) ||
		d.ResolvedType().Equivalent(exp)) {
		return errors.Errorf("expected return type %q, got: %q", exp, d.ResolvedType())
	}
	return nil
}

// arrayOfType returns a fresh DArray of the input type.
func arrayOfType(typ types.T) (*DArray, error) {
	arrayTyp, ok := typ.(types.TArray)
	if !ok {
		return nil, pgerror.NewAssertionErrorf("array node type (%v) is not types.TArray", typ)
	}
	if !types.IsValidArrayElementType(arrayTyp.Typ) {
		return nil, pgerror.NewErrorf(pgerror.CodeFeatureNotSupportedError, "arrays of %s not allowed", arrayTyp.Typ)
	}
	return NewDArray(arrayTyp.Typ), nil
}

// foldComparisonExpr folds a given comparison operation and its expressions
// into an equivalent operation that will hit in the CmpOps map, returning
// this new operation, along with potentially flipped operands and "flipped"
// and "not" flags.
func foldComparisonExpr(
	op ComparisonOperator, left, right Expr,
) (newOp ComparisonOperator, newLeft Expr, newRight Expr, flipped bool, not bool) {
	switch op {
	case NE:
		// NE(left, right) is implemented as !EQ(left, right).
		return EQ, left, right, false, true
	case GT:
		// GT(left, right) is implemented as LT(right, left)
		return LT, right, left, true, false
	case GE:
		// GE(left, right) is implemented as LE(right, left)
		return LE, right, left, true, false
	case NotIn:
		// NotIn(left, right) is implemented as !IN(left, right)
		return In, left, right, false, true
	case NotLike:
		// NotLike(left, right) is implemented as !Like(left, right)
		return Like, left, right, false, true
	case NotILike:
		// NotILike(left, right) is implemented as !ILike(left, right)
		return ILike, left, right, false, true
	case NotSimilarTo:
		// NotSimilarTo(left, right) is implemented as !SimilarTo(left, right)
		return SimilarTo, left, right, false, true
	case NotRegMatch:
		// NotRegMatch(left, right) is implemented as !RegMatch(left, right)
		return RegMatch, left, right, false, true
	case NotRegIMatch:
		// NotRegIMatch(left, right) is implemented as !RegIMatch(left, right)
		return RegIMatch, left, right, false, true
	case IsDistinctFrom:
		// IsDistinctFrom(left, right) is implemented as !IsNotDistinctFrom(left, right)
		// Note: this seems backwards, but IS NOT DISTINCT FROM is an extended
		// version of IS and IS DISTINCT FROM is an extended version of IS NOT.
		return IsNotDistinctFrom, left, right, false, true
	}
	return op, left, right, false, false
}

// hasUnescapedSuffix returns true if the ending byte is suffix and s has an
// even number of escapeTokens preceding suffix. Otherwise hasUnescapedSuffix
// will return false.
func hasUnescapedSuffix(s string, suffix byte, escapeToken string) bool {
	if s[len(s)-1] == suffix {
		var count int
		idx := len(s) - len(escapeToken) - 1
		for idx >= 0 && s[idx:idx+len(escapeToken)] == escapeToken {
			count++
			idx -= len(escapeToken)
		}
		return count%2 == 0
	}
	return false
}

// Simplifies LIKE/ILIKE expressions that do not need full regular expressions to
// evaluate the condition. For example, when the expression is just checking to see
// if a string starts with a given pattern.
func optimizedLikeFunc(
	pattern string, caseInsensitive bool, escape rune,
) (func(string) bool, error) {
	switch len(pattern) {
	case 0:
		return func(s string) bool {
			return s == ""
		}, nil
	case 1:
		switch pattern[0] {
		case '%':
			if escape == '%' {
				return nil, pgerror.NewErrorf(pgerror.CodeInvalidEscapeSequenceError, "LIKE pattern must not end with escape character")
			}
			return func(s string) bool {
				return true
			}, nil
		case '_':
			if escape == '_' {
				return nil, pgerror.NewErrorf(pgerror.CodeInvalidEscapeSequenceError, "LIKE pattern must not end with escape character")
			}
			return func(s string) bool {
				return len(s) == 1
			}, nil
		}
	default:
		if !strings.ContainsAny(pattern[1:len(pattern)-1], "_%") {
			// Patterns with even number of escape characters preceding the ending `%` will have
			// anyEnd set to true. Otherwise anyEnd will be set to false.
			anyEnd := hasUnescapedSuffix(pattern, '%', string(escape))
			// If '%' is the escape character, then it's not a wildcard.
			anyStart := pattern[0] == '%' && escape != '%'

			// Patterns with even number of escape characters preceding the ending `_` will have
			// singleAnyEnd set to true. Otherwise singleAnyEnd will be set to false.
			singleAnyEnd := hasUnescapedSuffix(pattern, '_', string(escape))
			// If '_' is the escape character, then it's not a wildcard.
			singleAnyStart := pattern[0] == '_' && escape != '_'

			// Since we've already checked for escaped characters
			// at the end, we can un-escape every character.
			// This is required since we do direct string
			// comparison.
			var err error
			if pattern, err = unescapePattern(pattern, string(escape), escape == '\\'); err != nil {
				return nil, err
			}
			switch {
			case anyEnd && anyStart:
				return func(s string) bool {
					substr := pattern[1 : len(pattern)-1]
					if caseInsensitive {
						s, substr = strings.ToUpper(s), strings.ToUpper(substr)
					}
					return strings.Contains(s, substr)
				}, nil

			case anyEnd:
				return func(s string) bool {
					prefix := pattern[:len(pattern)-1]
					if singleAnyStart {
						if len(s) == 0 {
							return false
						}

						prefix = prefix[1:]
						s = s[1:]
					}
					if caseInsensitive {
						s, prefix = strings.ToUpper(s), strings.ToUpper(prefix)
					}
					return strings.HasPrefix(s, prefix)
				}, nil

			case anyStart:
				return func(s string) bool {
					suffix := pattern[1:]
					if singleAnyEnd {
						if len(s) == 0 {
							return false
						}

						suffix = suffix[:len(suffix)-1]
						s = s[:len(s)-1]
					}
					if caseInsensitive {
						s, suffix = strings.ToUpper(s), strings.ToUpper(suffix)
					}
					return strings.HasSuffix(s, suffix)
				}, nil

			case singleAnyStart || singleAnyEnd:
				return func(s string) bool {
					if len(s) < 1 || (singleAnyStart && singleAnyEnd && len(s) < 2) {
						return false
					}

					if singleAnyStart {
						pattern = pattern[1:]
						s = s[1:]
					}

					if singleAnyEnd {
						pattern = pattern[:len(pattern)-1]
						s = s[:len(s)-1]
					}

					if caseInsensitive {
						s, pattern = strings.ToUpper(s), strings.ToUpper(pattern)
					}

					// We don't have to check for
					// prefixes/suffixes since we do not
					// have '%':
					//  - singleAnyEnd && anyStart handled
					//    in case anyStart
					//  - singleAnyStart && anyEnd handled
					//    in case anyEnd
					return s == pattern
				}, nil
			}
		}
	}
	return nil, nil
}

type likeKey struct {
	s               string
	caseInsensitive bool
	escape          rune
}

// unescapePattern unescapes a pattern for a given escape token.
// It handles escaped escape tokens properly by maintaining them as the escape
// token in the return string.
// For example, suppose we have escape token `\` (e.g. `B` is escaped in
// `A\BC` and `\` is escaped in `A\\C`).
// We need to convert
//    `\` --> ``
//    `\\` --> `\`
// We cannot simply use strings.Replace for each conversion since the first
// conversion will incorrectly replace our escaped escape token `\\` with ``.
// Another example is if our escape token is `\\` (e.g. after
// regexp.QuoteMeta).
// We need to convert
//    `\\` --> ``
//    `\\\\` --> `\\`
func unescapePattern(pattern, escapeToken string, isEscapeTokenCustom bool) (string, error) {
	escapedEscapeToken := escapeToken + escapeToken

	// We need to subtract the escaped escape tokens to avoid double
	// counting.
	nEscapes := strings.Count(pattern, escapeToken) - strings.Count(pattern, escapedEscapeToken)
	if nEscapes == 0 {
		return pattern, nil
	}

	// Allocate buffer for final un-escaped pattern.
	ret := make([]byte, len(pattern)-nEscapes*len(escapeToken))
	retWidth := 0
	for i := 0; i < nEscapes; i++ {
		nextIdx := strings.Index(pattern, escapeToken)
		if nextIdx == len(pattern)-len(escapeToken) && !isEscapeTokenCustom {
			return "", pgerror.NewErrorf(pgerror.CodeInvalidEscapeSequenceError, `LIKE pattern must not end with escape character`)
		}

		retWidth += copy(ret[retWidth:], pattern[:nextIdx])

		if nextIdx < len(pattern)-len(escapedEscapeToken) && pattern[nextIdx:nextIdx+len(escapedEscapeToken)] == escapedEscapeToken {
			// We have an escaped escape token.
			// We want to keep it as the original escape token in
			// the return string.
			retWidth += copy(ret[retWidth:], escapeToken)
			pattern = pattern[nextIdx+len(escapedEscapeToken):]
			continue
		}

		// Skip over the escape character we removed.
		pattern = pattern[nextIdx+len(escapeToken):]
	}

	retWidth += copy(ret[retWidth:], pattern)
	return string(ret[0:retWidth]), nil
}

// replaceUnescaped replaces all instances of oldStr that are not escaped (read:
// preceded) with the specified unescape token with newStr.
// For example, with an escape token of `\\`
//    replaceUnescaped("TE\\__ST", "_", ".", `\\`) --> "TE\\_.ST"
//    replaceUnescaped("TE\\%%ST", "%", ".*", `\\`) --> "TE\\%.*ST"
// If the preceding escape token is escaped, then oldStr will be replaced.
// For example
//    replaceUnescaped("TE\\\\_ST", "_", ".", `\\`) --> "TE\\\\.ST"
func replaceUnescaped(s, oldStr, newStr string, escapeToken string) string {
	// We count the number of occurrences of 'oldStr'.
	// This however can be an overestimate since the oldStr token could be
	// escaped.  e.g. `\\_`.
	nOld := strings.Count(s, oldStr)
	if nOld == 0 {
		return s
	}

	// Allocate buffer for final string.
	// This can be an overestimate since some of the oldStr tokens may
	// be escaped.
	// This is fine since we keep track of the running number of bytes
	// actually copied.
	// It's rather difficult to count the exact number of unescaped
	// tokens without manually iterating through the entire string and
	// keeping track of escaped escape tokens.
	retLen := len(s)
	// If len(newStr) - len(oldStr) < 0, then this can under-allocate which
	// will not behave correctly with copy.
	if addnBytes := nOld * (len(newStr) - len(oldStr)); addnBytes > 0 {
		retLen += addnBytes
	}
	ret := make([]byte, retLen)
	retWidth := 0
	start := 0
OldLoop:
	for i := 0; i < nOld; i++ {
		nextIdx := start + strings.Index(s[start:], oldStr)

		escaped := false
		for {
			// We need to look behind to check if the escape token
			// is really an escape token.
			// E.g. if our specified escape token is `\\` and oldStr
			// is `_`, then
			//    `\\_` --> escaped
			//    `\\\\_` --> not escaped
			//    `\\\\\\_` --> escaped
			curIdx := nextIdx
			lookbehindIdx := curIdx - len(escapeToken)
			for lookbehindIdx >= 0 && s[lookbehindIdx:curIdx] == escapeToken {
				escaped = !escaped
				curIdx = lookbehindIdx
				lookbehindIdx = curIdx - len(escapeToken)
			}

			// The token was not be escaped. Proceed.
			if !escaped {
				break
			}

			// Token was escaped. Copy everything over and continue.
			retWidth += copy(ret[retWidth:], s[start:nextIdx+len(oldStr)])
			start = nextIdx + len(oldStr)

			// Continue with next oldStr token.
			continue OldLoop
		}

		// Token was not escaped so we replace it with newStr.
		// Two copies is more efficient than concatenating the slices.
		retWidth += copy(ret[retWidth:], s[start:nextIdx])
		retWidth += copy(ret[retWidth:], newStr)
		start = nextIdx + len(oldStr)
	}

	retWidth += copy(ret[retWidth:], s[start:])
	return string(ret[0:retWidth])
}

// Replaces all custom escape characters in s with `\\` only when they are unescaped.          (1)
// E.g. original pattern       after QuoteMeta       after replaceCustomEscape with '@' as escape
//        '@w@w'          ->      '@w@w'        ->        '\\w\\w'
//        '@\@\'          ->      '@\\@\\'      ->        '\\\\\\\\'
//
// When an escape character is escaped, we replace it with its single occurrence.              (2)
// E.g. original pattern       after QuoteMeta       after replaceCustomEscape with '@' as escape
//        '@@w@w'         ->      '@@w@w'       ->        '@w\\w'
//        '@@@\'          ->      '@@@\\'       ->        '@\\\\'
//
// At the same time, we do not want to confuse original backslashes (which
// after QuoteMeta are '\\') with backslashes that replace our custom escape characters,
// so we escape these original backslashes again by converting '\\' into '\\\\'.               (3)
// E.g. original pattern       after QuoteMeta       after replaceCustomEscape with '@' as escape
//        '@\'            ->      '@\\'         ->        '\\\\\\'
//        '@\@@@\'        ->      '@\\@@@\\'    ->        '\\\\\\@\\\\\\'
//
// Explanation of the last example:
// 1. we replace '@' with '\\' since it's unescaped;
// 2. we escape single original backslash ('\' is not our escape character, so we want
// the pattern to understand it) by putting an extra backslash in front of it. However,
// we later will call unescapePattern, so we need to double our double backslahes.
// Therefore, '\\' is converted into '\\\\'.
// 3. '@@' is replaced by '@' because it is escaped escape character.
// 4. '@' is replaced with '\\' since it's unescaped.
// 5. Similar logic to step 2: '\\' -> '\\\\'.
//
// We always need to keep in mind that later call of unescapePattern
// to actually unescape '\\' and '\\\\' is necessary and that
// escape must be a single unicode character and not `\`.
func replaceCustomEscape(s string, escape rune) (string, error) {
	changed, retLen, err := calculateLengthAfterReplacingCustomEscape(s, escape)
	if err != nil {
		return "", err
	}
	if !changed {
		return s, nil
	}

	sLen := len(s)
	ret := make([]byte, retLen)
	retIndex, sIndex := 0, 0
	for retIndex < retLen {
		sRune, w := utf8.DecodeRuneInString(s[sIndex:])
		if sRune == escape {
			// We encountered an escape character.
			if sIndex+w < sLen {
				// Escape character is not the last character in s, so we need
				// to look ahead to figure out how to process it.
				tRune, _ := utf8.DecodeRuneInString(s[(sIndex + w):])
				if tRune == escape {
					// Escape character is escaped, so we replace its two occurrences with just one. See (2).
					// We copied only one escape character to ret, so we advance retIndex only by w.
					// Since we've already processed two characters in s, we advance sIndex by 2*w.
					utf8.EncodeRune(ret[retIndex:], escape)
					retIndex += w
					sIndex += 2 * w
				} else {
					// Escape character is unescaped, so we replace it with `\\`. See (1).
					// Since we've added two bytes to ret, we advance retIndex by 2.
					// We processed only a single escape character in s, we advance sIndex by w.
					ret[retIndex] = '\\'
					ret[retIndex+1] = '\\'
					retIndex += 2
					sIndex += w
				}
			} else {
				// Escape character is the last character in s which is an error
				// that must have been caught in calculateLengthAfterReplacingCustomEscape.
				panic("unexpected: escape character is the last one in replaceCustomEscape.")
			}
		} else if s[sIndex] == '\\' {
			// We encountered a backslash which after QuoteMeta should have been doubled.
			if sIndex+1 == sLen || s[sIndex+1] != '\\' {
				// This case should never be reached, and it should
				// have been caught in calculateLengthAfterReplacingCustomEscape.
				panic("unexpected: a backslash is not doubled in replaceCustomEscape.")
			}
			// We want to escape '\\' to `\\\\` for correct processing later by unescapePattern. See (3).
			// Since we've added four characters to ret, we advance retIndex by 4.
			// Since we've already processed two characters in s, we advance sIndex by 2.
			ret[retIndex] = '\\'
			ret[retIndex+1] = '\\'
			ret[retIndex+2] = '\\'
			ret[retIndex+3] = '\\'
			retIndex += 4
			sIndex += 2
		} else {
			// Regular character, so we simply copy it.
			ret[retIndex] = s[sIndex]
			retIndex++
			sIndex++
		}

	}
	return string(ret), nil
}

// calculateLengthAfterReplacingCustomEscape returns whether the pattern changes, the length
// of the resulting pattern after calling replaceCustomEscape, and any error if found.
func calculateLengthAfterReplacingCustomEscape(s string, escape rune) (bool, int, error) {
	changed := false
	retLen, sLen := 0, len(s)
	for i := 0; i < sLen; {
		sRune, w := utf8.DecodeRuneInString(s[i:])
		if sRune == escape {
			// We encountered an escape character.
			if i+w < sLen {
				// Escape character is not the last character in s, so we need
				// to look ahead to figure out how to process it.
				tRune, _ := utf8.DecodeRuneInString(s[(i + w):])
				if tRune == escape {
					// Escape character is escaped, so we'll replace its two occurrences with just one.
					// See (2) in the comment above replaceCustomEscape.
					changed = true
					retLen += w
					i += 2 * w
				} else {
					// Escape character is unescaped, so we'll replace it with `\\`.
					// See (1) in the comment above replaceCustomEscape.
					changed = true
					retLen += 2
					i += w
				}
			} else {
				// Escape character is the last character in s, so we need to return an error.
				return false, 0, pgerror.NewErrorf(pgerror.CodeInvalidEscapeSequenceError, "LIKE pattern must not end with escape character")
			}
		} else if s[i] == '\\' {
			// We encountered a backslash which after QuoteMeta should have been doubled.
			if i+1 == sLen || s[i+1] != '\\' {
				// This case should never be reached.
				return false, 0, pgerror.NewErrorf(pgerror.CodeInvalidEscapeSequenceError, "Unexpected behavior during processing custom escape character.")
			}
			// We'll want to escape '\\' to `\\\\` for correct processing later by unescapePattern.
			// See (3) in the comment above replaceCustomEscape.
			changed = true
			retLen += 4
			i += 2
		} else {
			// Regular character, so we'll simply copy it.
			retLen++
			i++
		}
	}
	return changed, retLen, nil
}

// Pattern implements the RegexpCacheKey interface.
// The strategy for handling custom escape character
// is to convert all unescaped escape character into '\'.
// k.escape can either be empty or a single character.
func (k likeKey) Pattern() (string, error) {
	// QuoteMeta escapes `\` to `\\`.
	pattern := regexp.QuoteMeta(k.s)
	var err error
	if k.escape == 0 {
		// Replace all LIKE/ILIKE specific wildcards with standard wildcards
		// (escape character is empty - escape mechanism is turned off - so
		// all '%' and '_' are actual wildcards regardless of what precedes them.
		pattern = strings.Replace(pattern, `%`, `.*`, -1)
		pattern = strings.Replace(pattern, `_`, `.`, -1)
	} else if k.escape == '\\' {
		// Replace LIKE/ILIKE specific wildcards with standard wildcards only when
		// these wildcards are not escaped by '\\' (equivalent of '\' after QuoteMeta).
		pattern = replaceUnescaped(pattern, `%`, `.*`, `\\`)
		pattern = replaceUnescaped(pattern, `_`, `.`, `\\`)
	} else {
		// k.escape is non-empty and not `\`.
		// If `%` is escape character, then it's not a wildcard.
		if k.escape != '%' {
			// Replace LIKE/ILIKE specific wildcards '%' only if it's unescaped.
			pattern = replaceUnescaped(pattern, `%`, `.*`, string(k.escape))
		}
		// If `_` is escape character, then it's not a wildcard.
		if k.escape != '_' {
			// Replace LIKE/ILIKE specific wildcards '_' only if it's unescaped.
			pattern = replaceUnescaped(pattern, `_`, `.`, string(k.escape))
		}

		// If a sequence of symbols ` escape+`\\` ` is unescaped, then that escape
		// character escapes backslash in the original pattern (we need to use double
		// backslash because of QuoteMeta behavior), so we want to "consume" the escape character.
		pattern = replaceUnescaped(pattern, string(k.escape)+`\\`, `\\`, string(k.escape))

		// We want to replace all escape characters with `\\` only
		// when they are unescaped. When an escape character is escaped,
		// we replace it with its single occurrence.
		if pattern, err = replaceCustomEscape(pattern, k.escape); err != nil {
			return pattern, err
		}
	}

	// After QuoteMeta, all '\' were converted to '\\'.
	// After replaceCustomEscape, our custom unescaped escape characters were converted to `\\`,
	// so now our pattern contains only '\\' as escape tokens.
	// We need to unescape escaped escape tokens `\\` (now `\\\\`) and
	// other escaped characters `\A` (now `\\A`).
	if k.escape != 0 {
		// We do not want to return an error when pattern ends with the supposed escape character `\`
		// whereas the actual escape character is not `\`. The case when the pattern ends with
		// an actual escape character is handled in replaceCustomEscape. For example, with '-' as
		// the escape character on pattern 'abc\\' we do not want to return an error 'pattern ends
		// with escape character' because '\\' is not an escape character in this case.
		if pattern, err = unescapePattern(pattern, `\\`, k.escape == '\\'); err != nil {
			return "", err
		}
	}

	return anchorPattern(pattern, k.caseInsensitive), nil
}

type similarToKey struct {
	s      string
	escape rune
}

// Pattern implements the RegexpCacheKey interface.
func (k similarToKey) Pattern() (string, error) {
	pattern := similarEscapeCustomChar(k.s, k.escape, k.escape != 0)
	return anchorPattern(pattern, false), nil
}

type regexpKey struct {
	s               string
	caseInsensitive bool
}

// Pattern implements the RegexpCacheKey interface.
func (k regexpKey) Pattern() (string, error) {
	if k.caseInsensitive {
		return caseInsensitive(k.s), nil
	}
	return k.s, nil
}

// SimilarEscape converts a SQL:2008 regexp pattern to POSIX style, so it can
// be used by our regexp engine.
func SimilarEscape(pattern string) string {
	return similarEscapeCustomChar(pattern, '\\', true)
}

// similarEscapeCustomChar converts a SQL:2008 regexp pattern to POSIX style,
// so it can be used by our regexp engine. This version of the function allows
// for a custom escape character.
// 'isEscapeNonEmpty' signals whether 'escapeChar' should be treated as empty.
func similarEscapeCustomChar(pattern string, escapeChar rune, isEscapeNonEmpty bool) string {
	patternBuilder := make([]rune, 0, utf8.RuneCountInString(pattern))

	inCharClass := false
	afterEscape := false
	numQuotes := 0
	for _, c := range pattern {
		switch {
		case afterEscape:
			// For SUBSTRING patterns
			if c == '"' && !inCharClass {
				if numQuotes%2 == 0 {
					patternBuilder = append(patternBuilder, '(')
				} else {
					patternBuilder = append(patternBuilder, ')')
				}
				numQuotes++
			} else if c == escapeChar && len(string(escapeChar)) > 1 {
				// We encountered escaped escape unicode character represented by at least two bytes,
				// so we keep only its single occurrence and need not to prepend it by '\'.
				patternBuilder = append(patternBuilder, c)
			} else {
				patternBuilder = append(patternBuilder, '\\', c)
			}
			afterEscape = false
		case utf8.ValidRune(escapeChar) && c == escapeChar && isEscapeNonEmpty:
			// SQL99 escape character; do not immediately send to output
			afterEscape = true
		case inCharClass:
			if c == '\\' {
				patternBuilder = append(patternBuilder, '\\')
			}
			patternBuilder = append(patternBuilder, c)
			if c == ']' {
				inCharClass = false
			}
		case c == '[':
			patternBuilder = append(patternBuilder, c)
			inCharClass = true
		case c == '%':
			patternBuilder = append(patternBuilder, '.', '*')
		case c == '_':
			patternBuilder = append(patternBuilder, '.')
		case c == '(':
			// Convert to non-capturing parenthesis
			patternBuilder = append(patternBuilder, '(', '?', ':')
		case c == '\\', c == '.', c == '^', c == '$':
			// Escape these characters because they are NOT
			// metacharacters for SQL-style regexp
			patternBuilder = append(patternBuilder, '\\', c)
		default:
			patternBuilder = append(patternBuilder, c)
		}
	}

	return string(patternBuilder)
}

// caseInsensitive surrounds the transformed input string with
//   (?i: ... )
// which uses a non-capturing set of parens to turn a case sensitive
// regular expression pattern into a case insensitive regular
// expression pattern.
func caseInsensitive(pattern string) string {
	return fmt.Sprintf("(?i:%s)", pattern)
}

// anchorPattern surrounds the transformed input string with
//   ^(?: ... )$
// which requires some explanation.  We need "^" and "$" to force
// the pattern to match the entire input string as per SQL99 spec.
// The "(?:" and ")" are a non-capturing set of parens; we have to have
// parens in case the string contains "|", else the "^" and "$" will
// be bound into the first and last alternatives which is not what we
// want, and the parens must be non capturing because we don't want them
// to count when selecting output for SUBSTRING.
func anchorPattern(pattern string, caseInsensitive bool) string {
	if caseInsensitive {
		return fmt.Sprintf("^(?i:%s)$", pattern)
	}
	return fmt.Sprintf("^(?:%s)$", pattern)
}

// IntPow computes the value of x^y.
func IntPow(x, y DInt) (*DInt, error) {
	xd := apd.New(int64(x), 0)
	yd := apd.New(int64(y), 0)
	_, err := DecimalCtx.Pow(xd, xd, yd)
	if err != nil {
		return nil, err
	}
	i, err := xd.Int64()
	if err != nil {
		return nil, errIntOutOfRange
	}
	return NewDInt(DInt(i)), nil
}

// PerformCast performs a cast from the provided Datum to the specified
// CastTargetType.
func PerformCast(d Datum, t coltypes.CastTargetType) (Datum, error) {
	switch typ := t.(type) {
	case *coltypes.TBitArray:
		switch v := d.(type) {
		case *DBitArray:
			if typ.Width == 0 || v.BitLen() == typ.Width {
				return d, nil
			}
			var a DBitArray
			a.BitArray = v.BitArray.ToWidth(typ.Width)
			return &a, nil
		case *DInt:
			return NewDBitArrayFromInt(int64(*v), typ.Width)
		case *DString:
			res, err := bitarray.Parse(string(*v))
			if err != nil {
				return nil, err
			}
			if typ.Width > 0 {
				res = res.ToWidth(typ.Width)
			}
			return &DBitArray{BitArray: res}, nil
		case *DCollatedString:
			res, err := bitarray.Parse(v.Contents)
			if err != nil {
				return nil, err
			}
			if typ.Width > 0 {
				res = res.ToWidth(typ.Width)
			}
			return &DBitArray{BitArray: res}, nil
		}

	case *coltypes.TBool:
		switch v := d.(type) {
		case *DBool:
			return d, nil
		case *DInt:
			return MakeDBool(*v != 0), nil
		case *DFloat:
			return MakeDBool(*v != 0), nil
		case *DDecimal:
			return MakeDBool(v.Sign() != 0), nil
		case *DString:
			return ParseDBool(string(*v))
		case *DCollatedString:
			return ParseDBool(v.Contents)
		}

	case *coltypes.TInt:
		var res *DInt
		switch v := d.(type) {
		case *DBitArray:
			res = v.AsDInt(uint(typ.Width))
		case *DBool:
			if *v {
				res = NewDInt(1)
			} else {
				res = DZero
			}
		case *DInt:
			// TODO(knz): enforce the coltype width here.
			res = v
		case *DFloat:
			f := float64(*v)
			// Use `<=` and `>=` here instead of just `<` and `>` because when
			// math.MaxInt64 and math.MinInt64 are converted to float64s, they are
			// rounded to numbers with larger absolute values. Note that the first
			// next FP value after and strictly greater than float64(math.MinInt64)
			// is -9223372036854774784 (= float64(math.MinInt64)+513) and the first
			// previous value and strictly smaller than float64(math.MaxInt64)
			// is 9223372036854774784 (= float64(math.MaxInt64)-513), and both are
			// convertible to int without overflow.
			if math.IsNaN(f) || f <= float64(math.MinInt64) || f >= float64(math.MaxInt64) {
				return nil, errIntOutOfRange
			}
			res = NewDInt(DInt(f))
		case *DDecimal:
			d := new(apd.Decimal)
			_, err := DecimalCtx.RoundToIntegralValue(d, &v.Decimal)
			if err != nil {
				return nil, err
			}
			i, err := d.Int64()
			if err != nil {
				return nil, errIntOutOfRange
			}
			res = NewDInt(DInt(i))
		case *DString:
			var err error
			if res, err = ParseDInt(string(*v)); err != nil {
				return nil, err
			}
		case *DCollatedString:
			var err error
			if res, err = ParseDInt(v.Contents); err != nil {
				return nil, err
			}
		case *DTimestamp:
			res = NewDInt(DInt(v.Unix()))
		case *DTimestampTZ:
			res = NewDInt(DInt(v.Unix()))
		case *DDate:
			res = NewDInt(DInt(int64(*v)))
		case *DInterval:
			iv, ok := v.AsInt64()
			if !ok {
				return nil, errIntOutOfRange
			}
			res = NewDInt(DInt(iv))
		case *DOid:
			res = &v.DInt
		}
		if res != nil {
			return res, nil
		}

	case *coltypes.TFloat:
		switch v := d.(type) {
		case *DBool:
			if *v {
				return NewDFloat(1), nil
			}
			return NewDFloat(0), nil
		case *DInt:
			return NewDFloat(DFloat(*v)), nil
		case *DFloat:
			return d, nil
		case *DDecimal:
			f, err := v.Float64()
			if err != nil {
				return nil, errFloatOutOfRange
			}
			return NewDFloat(DFloat(f)), nil
		case *DString:
			return ParseDFloat(string(*v))
		case *DCollatedString:
			return ParseDFloat(v.Contents)
		case *DTimestamp:
			micros := float64(v.Nanosecond() / int(time.Microsecond))
			return NewDFloat(DFloat(float64(v.Unix()) + micros*1e-6)), nil
		case *DTimestampTZ:
			micros := float64(v.Nanosecond() / int(time.Microsecond))
			return NewDFloat(DFloat(float64(v.Unix()) + micros*1e-6)), nil
		case *DDate:
			return NewDFloat(DFloat(float64(*v))), nil
		case *DInterval:
			return NewDFloat(DFloat(v.AsFloat64())), nil
		}

	case *coltypes.TDecimal:
		var dd DDecimal
		var err error
		unset := false
		switch v := d.(type) {
		case *DBool:
			if *v {
				dd.SetFinite(1, 0)
			}
		case *DInt:
			dd.SetFinite(int64(*v), 0)
		case *DDate:
			dd.SetFinite(int64(*v), 0)
		case *DFloat:
			_, err = dd.SetFloat64(float64(*v))
		case *DDecimal:
			// Small optimization to avoid copying into dd in normal case.
			if typ.Prec == 0 {
				return d, nil
			}
			dd = *v
		case *DString:
			err = dd.SetString(string(*v))
		case *DCollatedString:
			err = dd.SetString(v.Contents)
		case *DTimestamp:
			val := &dd.Coeff
			val.SetInt64(v.Unix())
			val.Mul(val, big10E6)
			micros := v.Nanosecond() / int(time.Microsecond)
			val.Add(val, big.NewInt(int64(micros)))
			dd.Exponent = -6
		case *DTimestampTZ:
			val := &dd.Coeff
			val.SetInt64(v.Unix())
			val.Mul(val, big10E6)
			micros := v.Nanosecond() / int(time.Microsecond)
			val.Add(val, big.NewInt(int64(micros)))
			dd.Exponent = -6
		case *DInterval:
			v.AsBigInt(&dd.Coeff)
			dd.Exponent = -9
		default:
			unset = true
		}
		if err != nil {
			return nil, err
		}
		if !unset {
			err = LimitDecimalWidth(&dd.Decimal, typ.Prec, typ.Scale)
			return &dd, err
		}

	case *coltypes.TString, *coltypes.TCollatedString, *coltypes.TName:
		var s string
		switch t := d.(type) {
		case *DBitArray:
			s = t.BitArray.String()
		case *DFloat:
			s = strconv.FormatFloat(float64(*t), 'g',
				15, 64)
		case *DBool, *DInt, *DDecimal:
			s = d.String()
		case *DTimestamp, *DTimestampTZ, *DDate, *DTime:
			s = AsStringWithFlags(d, FmtBareStrings)
		case *DTuple:
			s = AsStringWithFlags(d, FmtPgwireText)
		case *DArray:
			s = AsStringWithFlags(d, FmtPgwireText)
		case *DInterval:
			// When converting an interval to string, we need a string representation
			// of the duration (e.g. "5s") and not of the interval itself (e.g.
			// "INTERVAL '5s'").
			s = t.ValueAsString()
		case *DUuid:
			s = t.UUID.String()
		case *DIPAddr:
			s = t.String()
		case *DString:
			s = string(*t)
		case *DCollatedString:
			s = t.Contents
		case *DBytes:
			s = lex.EncodeByteArrayToRawBytes(string(*t),
				sessiondata.BytesEncodeHex, false /* skipHexPrefix */)
		case *DOid:
			s = t.name
		case *DJSON:
			s = t.JSON.String()
		}
		switch c := t.(type) {
		case *coltypes.TString:
			// If the string type specifies a limit we truncate to that limit:
			//   'hello'::CHAR(2) -> 'he'
			// This is true of all the string type variants.
			if c.N > 0 && c.N < uint(len(s)) {
				s = s[:c.N]
			}
			return NewDString(s), nil
		case *coltypes.TCollatedString:
			// Ditto truncation like for TString.
			if c.N > 0 && c.N < uint(len(s)) {
				s = s[:c.N]
			}
			return NewDCollatedString(s, c.Locale), nil
		case *coltypes.TName:
			return NewDName(s), nil
		}

	case *coltypes.TBytes:
		switch t := d.(type) {
		case *DString:
			return ParseDByte(string(*t))
		case *DCollatedString:
			return NewDBytes(DBytes(t.Contents)), nil
		case *DUuid:
			return NewDBytes(DBytes(t.GetBytes())), nil
		case *DBytes:
			return d, nil
		}

	case *coltypes.TUUID:
		switch t := d.(type) {
		case *DString:
			return ParseDUuidFromString(string(*t))
		case *DCollatedString:
			return ParseDUuidFromString(t.Contents)
		case *DBytes:
			return ParseDUuidFromBytes([]byte(*t))
		case *DUuid:
			return d, nil
		}

	case *coltypes.TIPAddr:
		switch t := d.(type) {
		case *DString:
			return ParseDIPAddrFromINetString(string(*t))
		case *DCollatedString:
			return ParseDIPAddrFromINetString(t.Contents)
		case *DIPAddr:
			return d, nil
		}

	case *coltypes.TDate:
		switch d := d.(type) {
		case *DString:
			return ParseDDate(string(*d), time.UTC)
		case *DCollatedString:
			return ParseDDate(d.Contents, time.UTC)
		case *DDate:
			return d, nil
		case *DInt:
			return NewDDate(DDate(int64(*d))), nil
		case *DTimestampTZ:
			return NewDDateFromTime(d.Time, time.UTC), nil
		case *DTimestamp:
			return NewDDateFromTime(d.Time, time.UTC), nil
		}

	case *coltypes.TTime:
		switch d := d.(type) {
		case *DString:
			return ParseDTime(string(*d))
		case *DCollatedString:
			return ParseDTime(d.Contents)
		case *DTime:
			return d, nil
		case *DTimestamp:
			return MakeDTime(timeofday.FromTime(d.Time)), nil
		case *DTimestampTZ:
			return MakeDTime(timeofday.FromTime(d.Time)), nil
		case *DInterval:
			return MakeDTime(timeofday.Min.Add(d.Duration)), nil
		}

	case *coltypes.TTimestamp:
		// TODO(knz): Timestamp from float, decimal.
		switch d := d.(type) {
		case *DString:
			return ParseDTimestamp(string(*d), time.Microsecond)
		case *DCollatedString:
			return ParseDTimestamp(d.Contents, time.Microsecond)
		case *DDate:
			year, month, day := timeutil.Unix(int64(*d)*SecondsInDay, 0).Date()
			return MakeDTimestamp(time.Date(year, month, day, 0, 0, 0, 0, time.UTC), time.Microsecond), nil
		case *DInt:
			return MakeDTimestamp(timeutil.Unix(int64(*d), 0), time.Second), nil
		case *DTimestamp:
			return d, nil
		case *DTimestampTZ:
			// Strip time zone. Timestamps don't carry their location.
			return d.stripTimeZone(), nil
		}

	case *coltypes.TTimestampTZ:
		// TODO(knz): TimestampTZ from float, decimal.
		switch d := d.(type) {
		case *DString:
			return ParseDTimestampTZ(string(*d), time.UTC, time.Microsecond)
		case *DCollatedString:
			return ParseDTimestampTZ(d.Contents, time.UTC, time.Microsecond)
		case *DDate:
			return MakeDTimestampTZFromDate(time.UTC, d), nil
		case *DTimestamp:
			_, before := d.Time.Zone()
			_, after := d.Time.In(time.UTC).Zone()
			return MakeDTimestampTZ(d.Time.Add(time.Duration(before-after)*time.Second), time.Microsecond), nil
		case *DInt:
			return MakeDTimestampTZ(timeutil.Unix(int64(*d), 0), time.Second), nil
		case *DTimestampTZ:
			return d, nil
		}

	case *coltypes.TInterval:
		switch v := d.(type) {
		case *DString:
			return ParseDInterval(string(*v))
		case *DCollatedString:
			return ParseDInterval(v.Contents)
		case *DInt:
			return &DInterval{Duration: duration.FromInt64(int64(*v))}, nil
		case *DFloat:
			return &DInterval{Duration: duration.FromFloat64(float64(*v))}, nil
		case *DTime:
			return &DInterval{Duration: duration.Duration{Nanos: int64(*v) * 1000}}, nil
		case *DDecimal:
			d := new(apd.Decimal)
			dnanos := v.Decimal
			dnanos.Exponent += 9
			// We need HighPrecisionCtx because duration values can contain
			// upward of 35 decimal digits and DecimalCtx only provides 25.
			_, err := HighPrecisionCtx.Quantize(d, &dnanos, 0)
			if err != nil {
				return nil, err
			}
			if dnanos.Negative {
				d.Coeff.Neg(&d.Coeff)
			}
			dv, ok := duration.FromBigInt(&d.Coeff)
			if !ok {
				return nil, errDecOutOfRange
			}
			return &DInterval{Duration: dv}, nil
		case *DInterval:
			return d, nil
		}
	case *coltypes.TJSON:
		switch v := d.(type) {
		case *DString:
			return ParseDJSON(string(*v))
		case *DJSON:
			return v, nil
		}
	case *coltypes.TArray:
		switch v := d.(type) {
		case *DString:
			return ParseDArrayFromString(string(*v), typ.ParamType)
		case *DArray:
			paramType := coltypes.CastTargetToDatumType(typ.ParamType)
			dcast := NewDArray(paramType)
			for _, e := range v.Array {
				ecast := DNull
				if e != DNull {
					var err error
					ecast, err = PerformCast(e, typ.ParamType)
					if err != nil {
						return nil, err
					}
				}

				if err := dcast.Append(ecast); err != nil {
					return nil, err
				}
			}
			return dcast, nil
		}
	case *coltypes.TOid:
		switch v := d.(type) {
		case *DOid:
			switch typ {
			case coltypes.Oid:
				return &DOid{semanticType: typ, DInt: v.DInt}, nil
			default:
				oid := NewDOid(v.DInt)
				oid.semanticType = typ
				return oid, nil
			}
		case *DInt:
			switch typ {
			case coltypes.Oid:
				return &DOid{semanticType: typ, DInt: *v}, nil
			default:
				oid := NewDOid(*v)
				oid.semanticType = typ
				return oid, nil
			}
		case *DString:
			s := string(*v)
			// Trim whitespace and unwrap outer quotes if necessary.
			// This is required to mimic postgres.
			s = strings.TrimSpace(s)
			if len(s) > 1 && s[0] == '"' && s[len(s)-1] == '"' {
				s = s[1 : len(s)-1]
			}

			return nil, pgerror.NewErrorf(pgerror.CodeSyntaxError,
				"cannot evaluate in parser: %s", s)
		}
	}

	return nil, pgerror.NewErrorf(
		pgerror.CodeCannotCoerceError, "invalid cast: %s -> %s", d.ResolvedType(), t)
}
