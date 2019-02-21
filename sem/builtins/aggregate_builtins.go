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

package builtins

import (
	"bytes"
	"fmt"

	apd "github.com/cockroachdb/apd/v2"
	"github.com/eandre/sqlparse/pkg/util/duration"
	"github.com/eandre/sqlparse/pkg/util/json"
	"github.com/eandre/sqlparse/sem/tree"
	"github.com/eandre/sqlparse/sem/types"
)

func initAggregateBuiltins() {
	// Add all aggregates to the Builtins map after a few sanity checks.
	for k, v := range aggregates {
		if !v.props.Impure {
			panic(fmt.Sprintf("%s: aggregate functions should all be impure, found %v", k, v))
		}
		if v.props.Class != tree.AggregateClass {
			panic(fmt.Sprintf("%s: aggregate functions should be marked with the tree.AggregateClass "+
				"function class, found %v", k, v))
		}

		// The aggregate functions are considered "row dependent". This is
		// because each aggregate function application receives the set of
		// grouped rows as implicit parameter. It may have a different
		// value in every group, so it cannot be considered constant in
		// the context of a data source.
		v.props.NeedsRepeatedEvaluation = true

		builtins[k] = v
	}
}

func aggProps() tree.FunctionProperties {
	return tree.FunctionProperties{Class: tree.AggregateClass, Impure: true}
}

func aggPropsNullableArgs() tree.FunctionProperties {
	f := aggProps()
	f.NullableArgs = true
	return f
}

// aggregates are a special class of builtin functions that are wrapped
// at execution in a bucketing layer to combine (aggregate) the result
// of the function being run over many rows.
//
// See `aggregateFuncHolder` in the sql package.
//
// In particular they must not be simplified during normalization
// (and thus must be marked as impure), even when they are given a
// constant argument (e.g. SUM(1)). This is because aggregate
// functions must return NULL when they are no rows in the source
// table, so their evaluation must always be delayed until query
// execution.
//
// Some aggregate functions must handle nullable arguments, since normalizing
// an aggregate function call to NULL in the presence of a NULL argument may
// not be correct. There are two cases where an aggregate function must handle
// nullable arguments:
// 1) the aggregate function does not skip NULLs (e.g., ARRAY_AGG); and
// 2) the aggregate function does not return NULL when it aggregates no rows
//		(e.g., COUNT).
//
// For use in other packages, see AllAggregateBuiltinNames and
// GetBuiltinProperties().
// These functions are also identified with Class == tree.AggregateClass.
// The properties are reachable via tree.FunctionDefinition.
var aggregates = map[string]builtinDefinition{
	"array_agg": setProps(aggPropsNullableArgs(),
		arrayBuiltin(func(t types.T) tree.Overload {
			return makeAggOverloadWithReturnType(
				[]types.T{t},
				func(args []tree.TypedExpr) types.T {
					if len(args) == 0 {
						return types.TArray{Typ: t}
					}
					// Whenever possible, use the expression's type, so we can properly
					// handle aliased types that don't explicitly have overloads.
					return types.TArray{Typ: args[0].ResolvedType()}
				},
				"Aggregates the selected values into an array.",
			)
		})),

	"avg": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Int}, types.Decimal,
			"Calculates the average of the selected values."),
		makeAggOverload([]types.T{types.Float}, types.Float,
			"Calculates the average of the selected values."),
		makeAggOverload([]types.T{types.Decimal}, types.Decimal,
			"Calculates the average of the selected values."),
	),

	"bool_and": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Bool}, types.Bool,
			"Calculates the boolean value of `AND`ing all selected values."),
	),

	"bool_or": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Bool}, types.Bool,
			"Calculates the boolean value of `OR`ing all selected values."),
	),

	"concat_agg": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.String}, types.String,
			"Concatenates all selected values."),
		makeAggOverload([]types.T{types.Bytes}, types.Bytes,
			"Concatenates all selected values."),
		// TODO(eisen): support collated strings when the type system properly
		// supports parametric types.
	),

	"count": makeBuiltin(aggPropsNullableArgs(),
		makeAggOverload([]types.T{types.Any}, types.Int,
			"Calculates the number of selected elements."),
	),

	"count_rows": makeBuiltin(aggProps(),
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Calculates the number of rows.",
		},
	),

	"max": collectOverloads(aggProps(), types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeAggOverload([]types.T{t}, t,
				"Identifies the maximum selected value.")
		}),

	"min": collectOverloads(aggProps(), types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeAggOverload([]types.T{t}, t,
				"Identifies the minimum selected value.")
		}),

	"string_agg": makeBuiltin(aggPropsNullableArgs(),
		makeAggOverload([]types.T{types.String, types.String}, types.String,
			"Concatenates all selected values using the provided delimiter."),
		makeAggOverload([]types.T{types.Bytes, types.Bytes}, types.Bytes,
			"Concatenates all selected values using the provided delimiter."),
	),

	"sum_int": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Int}, types.Int,
			"Calculates the sum of the selected values."),
	),

	"sum": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Int}, types.Decimal,
			"Calculates the sum of the selected values."),
		makeAggOverload([]types.T{types.Float}, types.Float,
			"Calculates the sum of the selected values."),
		makeAggOverload([]types.T{types.Decimal}, types.Decimal,
			"Calculates the sum of the selected values."),
		makeAggOverload([]types.T{types.Interval}, types.Interval,
			"Calculates the sum of the selected values."),
	),

	"sqrdiff": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Int}, types.Decimal,
			"Calculates the sum of squared differences from the mean of the selected values."),
		makeAggOverload([]types.T{types.Decimal}, types.Decimal,
			"Calculates the sum of squared differences from the mean of the selected values."),
		makeAggOverload([]types.T{types.Float}, types.Float,
			"Calculates the sum of squared differences from the mean of the selected values."),
	),

	// final_(variance|stddev) computes the global (variance|standard deviation)
	// from an arbitrary collection of local sums of squared difference from the mean.
	// Adapted from https://www.johndcook.com/blog/skewness_kurtosis and
	// https://github.com/cockroachdb/cockroach/pull/17728.

	// TODO(knz): The 3-argument final_variance and final_stddev are
	// only defined for internal use by distributed aggregations. They
	// are marked as "private" so as to not trigger panics from issue
	// #10495.

	// The input signature is: SQDIFF, SUM, COUNT
	"final_variance": makePrivate(makeBuiltin(aggProps(),
		makeAggOverload(
			[]types.T{types.Decimal, types.Decimal, types.Int},
			types.Decimal,
			"Calculates the variance from the selected locally-computed squared difference values.",
		),
		makeAggOverload(
			[]types.T{types.Float, types.Float, types.Int},
			types.Float,
			"Calculates the variance from the selected locally-computed squared difference values.",
		),
	)),

	"final_stddev": makePrivate(makeBuiltin(aggProps(),
		makeAggOverload(
			[]types.T{types.Decimal,
				types.Decimal, types.Int},
			types.Decimal,
			"Calculates the standard deviation from the selected locally-computed squared difference values.",
		),
		makeAggOverload(
			[]types.T{types.Float, types.Float, types.Int},
			types.Float,
			"Calculates the standard deviation from the selected locally-computed squared difference values.",
		),
	)),

	"variance": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Int}, types.Decimal,
			"Calculates the variance of the selected values."),
		makeAggOverload([]types.T{types.Decimal}, types.Decimal,
			"Calculates the variance of the selected values."),
		makeAggOverload([]types.T{types.Float}, types.Float,
			"Calculates the variance of the selected values."),
	),

	"stddev": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Int}, types.Decimal,
			"Calculates the standard deviation of the selected values."),
		makeAggOverload([]types.T{types.Decimal}, types.Decimal,
			"Calculates the standard deviation of the selected values."),
		makeAggOverload([]types.T{types.Float}, types.Float,
			"Calculates the standard deviation of the selected values."),
	),

	"xor_agg": makeBuiltin(aggProps(),
		makeAggOverload([]types.T{types.Bytes}, types.Bytes,
			"Calculates the bitwise XOR of the selected values."),
		makeAggOverload([]types.T{types.Int}, types.Int,
			"Calculates the bitwise XOR of the selected values."),
	),

	"json_agg": makeBuiltin(aggPropsNullableArgs(),
		makeAggOverload([]types.T{types.Any}, types.JSON,
			"Aggregates values as a JSON or JSONB array."),
	),

	"jsonb_agg": makeBuiltin(aggPropsNullableArgs(),
		makeAggOverload([]types.T{types.Any}, types.JSON,
			"Aggregates values as a JSON or JSONB array."),
	),

	AnyNotNull: makePrivate(makeBuiltin(aggProps(),
		makeAggOverloadWithReturnType(
			[]types.T{types.Any},
			tree.IdentityReturnType(0),
			"Returns an arbitrary not-NULL value, or NULL if none exists.",
		))),
}

// AnyNotNull is the name of the aggregate returned by NewAnyNotNullAggregate.
const AnyNotNull = "any_not_null"

func makePrivate(b builtinDefinition) builtinDefinition {
	b.props.Private = true
	return b
}

func makeAggOverload(
	in []types.T,
	ret types.T,
	info string,
) tree.Overload {
	return makeAggOverloadWithReturnType(
		in,
		tree.FixedReturnType(ret),
		info,
	)
}

func makeAggOverloadWithReturnType(
	in []types.T,
	retType tree.ReturnTyper,
	info string,
) tree.Overload {
	argTypes := make(tree.ArgTypes, len(in))
	for i, typ := range in {
		argTypes[i].Name = fmt.Sprintf("arg%d", i+1)
		argTypes[i].Typ = typ
	}

	return tree.Overload{
		// See the comment about aggregate functions in the definitions
		// of the Builtins array above.
		Types:      argTypes,
		ReturnType: retType,
		Info:       info,
	}
}

// See NewAnyNotNullAggregate.
type anyNotNullAggregate struct {
	val tree.Datum
}

type arrayAggregate struct {
	arr *tree.DArray
}

type avgAggregate struct {
	agg   tree.AggregateFunc
	count int
}

type concatAggregate struct {
	forBytes   bool
	sawNonNull bool
	delimiter  string // used for non window functions
	result     bytes.Buffer
}

type boolAndAggregate struct {
	sawNonNull bool
	result     bool
}

type boolOrAggregate struct {
	sawNonNull bool
	result     bool
}

type countAggregate struct {
	count int
}
type countRowsAggregate struct {
	count int
}

// MaxAggregate keeps track of the largest value passed to Add.
type MaxAggregate struct {
	max tree.Datum

	datumSize         uintptr
	variableDatumSize bool
}

// MinAggregate keeps track of the smallest value passed to Add.
type MinAggregate struct {
	min tree.Datum

	datumSize         uintptr
	variableDatumSize bool
}

type smallIntSumAggregate struct {
	sum         int64
	seenNonNull bool
}

type intSumAggregate struct {
	// Either the `intSum` and `decSum` fields contains the
	// result. Which one is used is determined by the `large` field
	// below.
	intSum      int64
	decSum      apd.Decimal
	tmpDec      apd.Decimal
	large       bool
	seenNonNull bool
}

type decimalSumAggregate struct {
	sum        apd.Decimal
	sawNonNull bool
}

type floatSumAggregate struct {
	sum        float64
	sawNonNull bool
}

type intervalSumAggregate struct {
	sum        duration.Duration
	sawNonNull bool
}

// Read-only constants used for square difference computations.
var (
	decimalOne = apd.New(1, 0)
	decimalTwo = apd.New(2, 0)
)

type floatSqrDiffAggregate struct {
	count   int64
	mean    float64
	sqrDiff float64
}

type decimalSqrDiffAggregate struct {
	// Variables used across iterations.
	ed      *apd.ErrDecimal
	count   apd.Decimal
	mean    apd.Decimal
	sqrDiff apd.Decimal

	// Variables used as scratch space within iterations.
	delta apd.Decimal
	tmp   apd.Decimal
}

type floatSumSqrDiffsAggregate struct {
	count   int64
	mean    float64
	sqrDiff float64
}

type decimalSumSqrDiffsAggregate struct {
	// Variables used across iterations.
	ed      *apd.ErrDecimal
	count   apd.Decimal
	mean    apd.Decimal
	sqrDiff apd.Decimal

	// Variables used as scratch space within iterations.
	tmpCount apd.Decimal
	tmpMean  apd.Decimal
	delta    apd.Decimal
	tmp      apd.Decimal
}

// Count is part of the decimalSqrDiff interface.
func (a *decimalSumSqrDiffsAggregate) Count() *apd.Decimal {
	return &a.count
}

// Tmp is part of the decimalSumSqrDiffs interface.
func (a *decimalSumSqrDiffsAggregate) Tmp() *apd.Decimal {
	return &a.tmp
}

type bytesXorAggregate struct {
	sum        []byte
	sawNonNull bool
}
type intXorAggregate struct {
	sum        int64
	sawNonNull bool
}
type jsonAggregate struct {
	builder    *json.ArrayBuilderWithCounter
	sawNonNull bool
}
