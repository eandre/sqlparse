// Copyright 2016 The Cockroach Authors.
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
	"fmt"

	"github.com/eandre/sqlparse/pkg/util/pgerror"
	"github.com/eandre/sqlparse/sem/tree"
	"github.com/eandre/sqlparse/sem/types"
)

func initWindowBuiltins() {
	// Add all windows to the Builtins map after a few sanity checks.
	for k, v := range windows {
		if !v.props.Impure {
			panic(fmt.Sprintf("%s: window functions should all be impure, found %v", k, v))
		}
		if v.props.Class != tree.WindowClass {
			panic(fmt.Sprintf("%s: window functions should be marked with the tree.WindowClass "+
				"function class, found %v", k, v))
		}
		builtins[k] = v
	}
}

func winProps() tree.FunctionProperties {
	return tree.FunctionProperties{
		Impure: true,
		Class:  tree.WindowClass,
	}
}

// windows are a special class of builtin functions that can only be applied
// as window functions using an OVER clause.
// See `windowFuncHolder` in the sql package.
var windows = map[string]builtinDefinition{
	"row_number": makeBuiltin(winProps(),
		makeWindowOverload(tree.ArgTypes{}, types.Int,
			"Calculates the number of the current row within its partition, counting from 1."),
	),
	"rank": makeBuiltin(winProps(),
		makeWindowOverload(tree.ArgTypes{}, types.Int,
			"Calculates the rank of the current row with gaps; same as row_number of its first peer."),
	),
	"dense_rank": makeBuiltin(winProps(),
		makeWindowOverload(tree.ArgTypes{}, types.Int,
			"Calculates the rank of the current row without gaps; this function counts peer groups."),
	),
	"percent_rank": makeBuiltin(winProps(),
		makeWindowOverload(tree.ArgTypes{}, types.Float,
			"Calculates the relative rank of the current row: (rank - 1) / (total rows - 1)."),
	),
	"cume_dist": makeBuiltin(winProps(),
		makeWindowOverload(tree.ArgTypes{}, types.Float,
			"Calculates the relative rank of the current row: "+
				"(number of rows preceding or peer with current row) / (total rows)."),
	),
	"ntile": makeBuiltin(winProps(),
		makeWindowOverload(tree.ArgTypes{{"n", types.Int}}, types.Int,
			"Calculates an integer ranging from 1 to `n`, dividing the partition as equally as possible."),
	),
	"lag": collectOverloads(
		winProps(),
		types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{{"val", t}}, t,
				"Returns `val` evaluated at the previous row within current row's partition; "+
					"if there is no such row, instead returns null.")
		},
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{{"val", t}, {"n", types.Int}}, t,
				"Returns `val` evaluated at the row that is `n` rows before the current row within its partition; "+
					"if there is no such row, instead returns null. `n` is evaluated with respect to the current row.")
		},
		// TODO(nvanbenschoten): We still have no good way to represent two parameters that
		// can be any types but must be the same (eg. lag(T, Int, T)).
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{
				{"val", t}, {"n", types.Int}, {"default", t},
			}, t,
				"Returns `val` evaluated at the row that is `n` rows before the current row within its partition; "+
					"if there is no such, row, instead returns `default` (which must be of the same type as `val`). "+
					"Both `n` and `default` are evaluated with respect to the current row.")
		},
	),
	"lead": collectOverloads(winProps(), types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{{"val", t}}, t,
				"Returns `val` evaluated at the following row within current row's partition; "+""+
					"if there is no such row, instead returns null.")
		},
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{{"val", t}, {"n", types.Int}}, t,
				"Returns `val` evaluated at the row that is `n` rows after the current row within its partition; "+
					"if there is no such row, instead returns null. `n` is evaluated with respect to the current row.")
		},
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{
				{"val", t}, {"n", types.Int}, {"default", t},
			}, t,
				"Returns `val` evaluated at the row that is `n` rows after the current row within its partition; "+
					"if there is no such, row, instead returns `default` (which must be of the same type as `val`). "+
					"Both `n` and `default` are evaluated with respect to the current row.")
		},
	),
	"first_value": collectOverloads(winProps(), types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{{"val", t}}, t,
				"Returns `val` evaluated at the row that is the first row of the window frame.")
		}),
	"last_value": collectOverloads(winProps(), types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{{"val", t}}, t,
				"Returns `val` evaluated at the row that is the last row of the window frame.")
		}),
	"nth_value": collectOverloads(winProps(), types.AnyNonArray,
		func(t types.T) tree.Overload {
			return makeWindowOverload(tree.ArgTypes{
				{"val", t}, {"n", types.Int}}, t,
				"Returns `val` evaluated at the row that is the `n`th row of the window frame (counting from 1); "+
					"null if no such row.")
		}),
}

func makeWindowOverload(
	in tree.ArgTypes, ret types.T, info string,
) tree.Overload {
	return tree.Overload{
		Types:      in,
		ReturnType: tree.FixedReturnType(ret),
		Info:       info,
	}
}

const noFilterIdx = -1

// aggregateWindowFunc aggregates over the the current row's window frame, using
// the internal tree.AggregateFunc to perform the aggregation.
type aggregateWindowFunc struct {
	agg     tree.AggregateFunc
	peerRes tree.Datum
}

// framableAggregateWindowFunc is a wrapper around aggregateWindowFunc that allows
// to reset the aggregate by creating a new instance via a provided constructor.
// shouldReset indicates whether the resetting behavior is desired.
type framableAggregateWindowFunc struct {
	shouldReset bool
}

// rowNumberWindow computes the number of the current row within its partition,
// counting from 1.
type rowNumberWindow struct{}

// rankWindow computes the rank of the current row with gaps.
type rankWindow struct {
	peerRes *tree.DInt
}

// denseRankWindow computes the rank of the current row without gaps (it counts peer groups).
type denseRankWindow struct {
	denseRank int
	peerRes   *tree.DInt
}

// percentRankWindow computes the relative rank of the current row using:
//   (rank - 1) / (total rows - 1)
type percentRankWindow struct {
	peerRes *tree.DFloat
}

var dfloatZero = tree.NewDFloat(0)

// cumulativeDistWindow computes the relative rank of the current row using:
//   (number of rows preceding or peer with current row) / (total rows)
type cumulativeDistWindow struct {
	peerRes *tree.DFloat
}

// ntileWindow computes an integer ranging from 1 to the argument value, dividing
// the partition as equally as possible.
type ntileWindow struct {
	ntile          *tree.DInt // current result
	curBucketCount int        // row number of current bucket
	boundary       int        // how many rows should be in the bucket
	remainder      int        // (total rows) % (bucket num)
}

var errInvalidArgumentForNtile = pgerror.NewErrorf(
	pgerror.CodeInvalidParameterValueError, "argument of ntile() must be greater than zero")

type leadLagWindow struct {
	forward     bool
	withOffset  bool
	withDefault bool
}

// firstValueWindow returns value evaluated at the row that is the first row of the window frame.
type firstValueWindow struct{}

// lastValueWindow returns value evaluated at the row that is the last row of the window frame.
type lastValueWindow struct{}

// nthValueWindow returns value evaluated at the row that is the nth row of the window frame
// (counting from 1). Returns null if no such row.
type nthValueWindow struct{}

var errInvalidArgumentForNthValue = pgerror.NewErrorf(
	pgerror.CodeInvalidParameterValueError, "argument of nth_value() must be greater than zero")
