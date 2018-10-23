// Copyright 2018 The Cockroach Authors.
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
	"github.com/eandre/sqlparse/pkg/util/ring"
)

// PeerGroupChecker can check if a pair of row indices within a partition are
// in the same peer group.
type PeerGroupChecker interface {
	InSameGroup(i, j int) bool
}

// peerGroup contains information about a single peer group.
type peerGroup struct {
	firstPeerIdx int
	rowCount     int
}

// PeerGroupsIndicesHelper computes peer groups using the given
// PeerGroupChecker. In ROWS and RANGE modes, it processes one peer group at
// a time and stores information only about single peer group. In GROUPS mode,
// it's behavior depends on the frame bounds; in the worst case, it stores
// max(F, O) peer groups at the same time, where F is the maximum number of
// peer groups within the frame at any point and O is the maximum of two
// offsets if we have OFFSET_FOLLOWING type of bound (both F and O are
// upper-bounded by total number of peer groups).
type PeerGroupsIndicesHelper struct {
	groups               ring.Buffer // queue of peer groups
	peerGrouper          PeerGroupChecker
	headPeerGroupNum     int  // number of the peer group at the head of the queue
	allPeerGroupsSkipped bool // in GROUP mode, indicates whether all peer groups were skipped during Init
	allRowsProcessed     bool // indicates whether peer groups for all rows within partition have been already computed
	unboundedFollowing   int  // index of the first row after all rows of the partition
}

// GetFirstPeerIdx returns index of the first peer within peer group of number
// peerGroupNum (counting from 0).
func (p *PeerGroupsIndicesHelper) GetFirstPeerIdx(peerGroupNum int) int {
	if p.allPeerGroupsSkipped {
		// Special case: we have skipped all peer groups in Init, so the frame is
		// always empty. It happens only with frames like GROUPS 100 FOLLOWING
		// which (if we have less than 100 peer groups total) behaves exactly like
		// GROUPS UNBOUNDED FOLLOWING (if it were allowed).
		return p.unboundedFollowing
	}
	posInBuffer := peerGroupNum - p.headPeerGroupNum
	if posInBuffer < 0 || p.groups.Len() < posInBuffer {
		panic("peerGroupNum out of bounds")
	}
	return p.groups.Get(posInBuffer).(*peerGroup).firstPeerIdx
}

// GetRowCount returns the number of rows within peer group of number
// peerGroupNum (counting from 0).
func (p *PeerGroupsIndicesHelper) GetRowCount(peerGroupNum int) int {
	if p.allPeerGroupsSkipped {
		// Special case: we have skipped all peer groups in Init, so the frame is
		// always empty. It happens only with frames like GROUPS 100 FOLLOWING
		// if we have less than 100 peer groups total.
		return 0
	}
	posInBuffer := peerGroupNum - p.headPeerGroupNum
	if posInBuffer < 0 || p.groups.Len() < posInBuffer {
		panic("peerGroupNum out of bounds")
	}
	return p.groups.Get(posInBuffer).(*peerGroup).rowCount
}

// GetLastPeerGroupNum returns the number of the last peer group in the queue.
func (p *PeerGroupsIndicesHelper) GetLastPeerGroupNum() int {
	if p.groups.Len() == 0 {
		panic("GetLastPeerGroupNum on empty RingBuffer")
	}
	return p.headPeerGroupNum + p.groups.Len() - 1
}
