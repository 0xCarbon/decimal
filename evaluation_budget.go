// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
	"runtime"
)

// evaluationStatus avoids allocated public errors inside nested evaluation.
// A zero code is success. A resource identifies only a supplied-quota refusal.
type evaluationStatus struct {
	code     ErrorCode
	resource EvaluationResource
	limit    uint64
}

type evaluationMeter struct {
	budget    Budget
	remaining uint64
	liveBytes uint64
	spent     uint64 // finite charges so far: MaxWork − remaining unless reset
}

// evaluationAllocation belongs to exactly one owner, not each borrowed view.
// bytes is its conservative physical-addressability size, distinct from the
// cumulative allocator envelope already charged to the unit quota.
type evaluationAllocation struct{ bytes uint64 }

func newEvaluationMeter(budget Budget) evaluationMeter {
	return evaluationMeter{budget: budget, remaining: budget.MaxWork}
}

func (m *evaluationMeter) unitRefusal() evaluationStatus {
	return evaluationStatus{code: ErrInsufficientStorage, resource: EvaluationUnits, limit: m.budget.MaxWork}
}

// phase admits independently proved arithmetic/allocation envelopes. Unlimited
// calls do not accumulate a lifetime uint64 counter and cannot overflow one.
func (m *evaluationMeter) phase(a, h uint64) evaluationStatus {
	if m.budget.MaxWork == 0 {
		return evaluationStatus{}
	}
	q, carry := bits.Add64(a, h, 0)
	q, extra := bits.Add64(q, 1, 0)
	if carry != 0 || extra != 0 || q > m.remaining {
		return m.unitRefusal()
	}
	m.remaining -= q
	m.spent += q
	return evaluationStatus{}
}

// admitObject reserves an explicit object's quota and live ownership before
// the caller executes make/new. No actual allocation occurs here. The caller
// must request the full capacity and release only when its owned object is no
// longer needed. This is addressability admission, not available-RAM prediction.
func (m *evaluationMeter) admitObject(rawBytes uint64) (evaluationAllocation, evaluationStatus) {
	var tally costTally
	heap := allocBound(&tally, rawBytes)
	if tally.overflow {
		if m.budget.MaxWork != 0 {
			return evaluationAllocation{}, m.unitRefusal()
		}
		return evaluationAllocation{}, evaluationStatus{code: ErrInsufficientStorage}
	}
	if s := m.phase(rawBytes, heap); s.code != 0 {
		return evaluationAllocation{}, s
	}
	physical, s := m.addressable(rawBytes)
	if s.code != 0 {
		return evaluationAllocation{}, s
	}
	m.liveBytes += physical
	return evaluationAllocation{bytes: physical}, evaluationStatus{}
}

// physical checks that a published object of rawBytes stays addressable
// beside the live arenas. Its allocator envelope is charged by the caller;
// the published result is owned by the caller and never released here.
func (m *evaluationMeter) physical(rawBytes uint64) evaluationStatus {
	_, s := m.addressable(rawBytes)
	return s
}

func (m *evaluationMeter) addressable(rawBytes uint64) (uint64, evaluationStatus) {
	maxObject, maxAddress, ok := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	physical, rounded := bigIntRoundObject(rawBytes)
	live, carry := bits.Add64(m.liveBytes, physical, 0)
	if !ok || !rounded || rawBytes > uint64(math.MaxInt) || physical > maxObject || carry != 0 || live > maxAddress {
		return 0, evaluationStatus{code: ErrInsufficientStorage}
	}
	return physical, evaluationStatus{}
}

// release never refunds work or cumulative allocation. Invalid internal
// ownership fails closed for subsequent physical admission instead of wrapping.
func (m *evaluationMeter) release(allocation evaluationAllocation) {
	if allocation.bytes > m.liveBytes {
		m.liveBytes = math.MaxUint64
		return
	}
	m.liveBytes -= allocation.bytes
}

func (m *evaluationMeter) resultDigits(n uint64) evaluationStatus {
	n = max(n, 1)
	if m.budget.MaxDigits != 0 && n > m.budget.MaxDigits {
		return evaluationStatus{code: ErrInsufficientStorage, resource: EvaluationCoefficientDigits, limit: m.budget.MaxDigits}
	}
	return evaluationStatus{}
}

// evaluationFailure constructs the one outer public error after internal work
// has stopped. Embedded Error is stored by value in the quota object.
func evaluationFailure(op string, s evaluationStatus) error {
	if s.code == 0 {
		return nil
	}
	if s.resource != 0 {
		return &Error{Op: op, Code: ErrInsufficientStorage, Condition: InsufficientStorage, Resource: s.resource, Limit: s.limit}
	}
	return newError(op, s.code)
}
