// Copyright 2017 The Cockroach Authors.
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
	"github.com/eandre/sqlparse/sem/types"
)

// IndexedRows are rows with the corresponding indices.
type IndexedRows interface {
	Len() int                  // returns number of rows
	GetRow(idx int) IndexedRow // returns a row at the given index
}

// IndexedRow is a row with a corresponding index.
type IndexedRow interface {
	GetIdx() int                           // returns index of the row
	GetDatum(idx int) Datum                // returns a datum at the given index
	GetDatums(startIdx, endIdx int) Datums // returns datums at indices [startIdx, endIdx)
}

// WindowFrameRangeOps allows for looking up an implementation of binary
// operators necessary for RANGE mode of framing.
type WindowFrameRangeOps struct{}

// LookupImpl looks up implementation of Plus and Minus binary operators for
// provided left and right types and returns them along with a boolean which
// indicates whether lookup is successful.
func (o WindowFrameRangeOps) LookupImpl(left, right types.T) (*BinOp, *BinOp, bool) {
	plusOverloads, minusOverloads := BinOps[Plus], BinOps[Minus]
	plusOp, found := plusOverloads.lookupImpl(left, right)
	if !found {
		return nil, nil, false
	}
	minusOp, found := minusOverloads.lookupImpl(left, right)
	if !found {
		return nil, nil, false
	}
	return plusOp, minusOp, true
}

// WindowFunc performs a computation on each row using data from a provided *WindowFrameRun.
type WindowFunc interface {
	WindowFuncMarker()
}
