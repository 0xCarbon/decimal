// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"hash/maphash"
	"math/big"
	"strconv"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

type f5Slot struct {
	key   decimal.Decimal
	hash  uint64
	cycle uint64
	value int
	state uint8 // 1 occupied, 2 deleted within the current cycle
}

// f5HashTable is a consumer-owned benchmark adapter, not a library API.
// Its fixed 2048 slots keep the 1024-entry load at one half. A new cycle
// makes old tombstones invisible in constant work except at epoch wrap,
// when the slots are cleared. Probe cost cannot accumulate across churn.
type f5HashTable struct {
	slots  []f5Slot
	seed   maphash.Seed
	hasher decimal.Hasher
	cycle  uint64
	count  int
}

func newF5HashTable() *f5HashTable {
	return &f5HashTable{slots: make([]f5Slot, 2048), seed: maphash.MakeSeed(), cycle: 1}
}

func (t *f5HashTable) digest(key decimal.Decimal) uint64 {
	var h maphash.Hash
	h.SetSeed(t.seed)
	t.hasher.Hash(&h, key)
	return h.Sum64()
}

func (t *f5HashTable) nextCycle() bool {
	if t.count != 0 {
		return false
	}
	t.cycle++
	if t.cycle == 0 {
		clear(t.slots)
		t.cycle = 1
	}
	return true
}

func (t *f5HashTable) put(key decimal.Decimal, value int) bool {
	return t.putAt(t.digest(key), key, value)
}

func (t *f5HashTable) putAt(hash uint64, key decimal.Decimal, value int) bool {
	mask := uint64(len(t.slots) - 1)
	firstDeleted := -1
	for step := range len(t.slots) {
		index := int((hash + uint64(step)) & mask)
		slot := &t.slots[index]
		if slot.cycle != t.cycle {
			if firstDeleted >= 0 {
				slot = &t.slots[firstDeleted]
			}
			*slot = f5Slot{key: key, hash: hash, cycle: t.cycle, value: value, state: 1}
			t.count++
			return true
		}
		if slot.state == 2 {
			if firstDeleted < 0 {
				firstDeleted = index
			}
			continue
		}
		if slot.hash == hash && t.hasher.Equal(slot.key, key) {
			slot.value = value
			return true
		}
	}
	if firstDeleted >= 0 {
		t.slots[firstDeleted] = f5Slot{key: key, hash: hash, cycle: t.cycle, value: value, state: 1}
		t.count++
		return true
	}
	return false
}

func (t *f5HashTable) getAt(hash uint64, key decimal.Decimal) (int, bool) {
	mask := uint64(len(t.slots) - 1)
	for step := range len(t.slots) {
		slot := &t.slots[int((hash+uint64(step))&mask)]
		if slot.cycle != t.cycle {
			return 0, false
		}
		if slot.state == 1 && slot.hash == hash && t.hasher.Equal(slot.key, key) {
			return slot.value, true
		}
	}
	return 0, false
}

func (t *f5HashTable) take(key decimal.Decimal) (int, bool) {
	return t.takeAt(t.digest(key), key)
}

func (t *f5HashTable) takeAt(hash uint64, key decimal.Decimal) (int, bool) {
	mask := uint64(len(t.slots) - 1)
	for step := range len(t.slots) {
		slot := &t.slots[int((hash+uint64(step))&mask)]
		if slot.cycle != t.cycle {
			return 0, false
		}
		if slot.state == 1 && slot.hash == hash && t.hasher.Equal(slot.key, key) {
			value := slot.value
			slot.key = decimal.Decimal{}
			slot.state = 2
			t.count--
			return value, true
		}
	}
	return 0, false
}

func (t *f5HashTable) deleteAt(hash uint64, key decimal.Decimal) bool {
	_, ok := t.takeAt(hash, key)
	return ok
}

func TestF5HasherTableTake(t *testing.T) {
	table := newF5HashTable()
	base := [...]decimal.Decimal{
		decimal.MustParse("1.20"),
		decimal.MustParse("2.30"),
		decimal.MustParse("3.40"),
	}
	cohort := [...]decimal.Decimal{
		decimal.MustParse("1.200"),
		decimal.MustParse("2.300"),
		decimal.MustParse("3.400"),
	}
	const collision = uint64(7)
	for i, key := range base {
		if !table.putAt(collision, key, i) {
			t.Fatal("failed to fill collision chain")
		}
	}
	if got, ok := table.takeAt(collision, cohort[1]); !ok || got != 1 || table.count != 2 {
		t.Fatalf("take in collision chain: got %d, present %v, count %d", got, ok, table.count)
	}
	if got, ok := table.getAt(collision, cohort[1]); ok {
		t.Fatalf("taken key remains present with value %d", got)
	}
	if got, ok := table.takeAt(collision, cohort[2]); !ok || got != 2 {
		t.Fatalf("take beyond tombstone: got %d, present %v", got, ok)
	}
	if got, ok := table.takeAt(collision, cohort[1]); ok {
		t.Fatalf("repeated take found value %d", got)
	}
	if got, ok := table.takeAt(collision, decimal.MustParse("9.90")); ok {
		t.Fatalf("missing key returned %d", got)
	}
	if got, ok := table.takeAt(collision, cohort[0]); !ok || got != 0 || table.count != 0 {
		t.Fatalf("final take: got %d, present %v, count %d", got, ok, table.count)
	}
	if !table.nextCycle() {
		t.Fatal("nonempty table at next cycle")
	}
	if !table.put(base[0], 42) {
		t.Fatal("failed to insert normally hashed key")
	}
	if got, ok := table.take(cohort[0]); !ok || got != 42 || table.count != 0 {
		t.Fatalf("normal hashed take: got %d, present %v, count %d", got, ok, table.count)
	}
}

// f5ExpectedKey uses the committed four-integer/two-fraction corpus shape,
// independently of Decimal's Reduce and Text methods. A reduced member with
// positive exponent uses the scientific canonical form.
func f5ExpectedKey(input string) string {
	digits := input[:4] + input[5:]
	exponent := -2
	for strings.HasSuffix(digits, "0") {
		digits = digits[:len(digits)-1]
		exponent++
	}
	if exponent > 0 {
		adjusted := strconv.Itoa(len(digits) - 1 + exponent)
		if len(digits) == 1 {
			return digits + "E+" + adjusted
		}
		return digits[:1] + "." + digits[1:] + "E+" + adjusted
	}
	if exponent == 0 {
		return digits
	}
	point := len(digits) + exponent
	return digits[:point] + "." + digits[point:]
}

func benchF5MapKey(b *testing.B) {
	pairs := portfolioF5Inputs
	values := make([]decimal.Decimal, len(pairs))
	cohorts := make([]decimal.Decimal, len(pairs))
	wantKeys := make([]string, 0, 2*len(pairs))
	gotKeys := make([]string, 0, 2*len(pairs))
	for i, pair := range pairs {
		var err error
		values[i], err = decimal.Parse(pair.base)
		if err != nil {
			b.Fatal(err)
		}
		cohorts[i], err = decimal.Parse(pair.cohort)
		if err != nil {
			b.Fatal(err)
		}
		left, ok := new(big.Rat).SetString(pair.base)
		if !ok {
			b.Fatalf("invalid F5 corpus input %q", pair.base)
		}
		right, ok := new(big.Rat).SetString(pair.cohort)
		if !ok || left.Cmp(right) != 0 || !values[i].Equal(cohorts[i]) || values[i].Compare(cohorts[i]) != 0 {
			b.Fatalf("F5 cohort mismatch: %q / %q", pair.base, pair.cohort)
		}
		want := f5ExpectedKey(pair.base)
		for _, value := range [...]decimal.Decimal{values[i], cohorts[i]} {
			key, err := value.Reduce().Text(0)
			if err != nil {
				b.Fatal(err)
			}
			gotKeys = append(gotKeys, key)
			wantKeys = append(wantKeys, want)
		}
	}

	b.Run("decimal/string1024", func(b *testing.B) {
		requireMatchedAccuracy(b, "F5MapKey/string1024", gotKeys, wantKeys)
		m := make(map[string]int, len(pairs))
		b.ReportAllocs()
		b.ResetTimer()
		for b.Loop() {
			for i, value := range values {
				key, err := value.Reduce().Text(0)
				if err != nil {
					b.Fatal(err)
				}
				m[key] = i
			}
			for i, value := range cohorts {
				key, err := value.Reduce().Text(0)
				if err != nil {
					b.Fatal(err)
				}
				if got, ok := m[key]; !ok || got != i {
					b.Fatalf("F5 string key %d mismatch: got %d, present %v", i, got, ok)
				}
				delete(m, key)
			}
			if len(m) != 0 {
				b.Fatalf("F5 string map retained %d entries", len(m))
			}
		}
	})

	b.Run("decimal/hasher1024", func(b *testing.B) {
		table := newF5HashTable()
		got := make([]string, len(pairs))
		want := make([]string, len(pairs))
		for i, value := range values {
			if !table.put(value, i) {
				b.Fatal("F5 table full during accuracy setup")
			}
		}
		for i, value := range cohorts {
			result, ok := table.take(value)
			if !ok {
				b.Fatalf("F5 Hasher cohort %d not found during accuracy setup", i)
			}
			got[i], want[i] = strconv.Itoa(result), strconv.Itoa(i)
		}
		if table.count != 0 {
			b.Fatalf("F5 table retained %d entries after accuracy setup", table.count)
		}
		requireMatchedAccuracy(b, "F5MapKey/hasher1024", got, want)
		b.ReportAllocs()
		b.ResetTimer()
		for b.Loop() {
			if !table.nextCycle() {
				b.Fatal("F5 table not empty before churn")
			}
			for i, value := range values {
				if !table.put(value, i) {
					b.Fatal("F5 table full during churn")
				}
			}
			for i, value := range cohorts {
				result, ok := table.take(value)
				if !ok || result != i {
					b.Fatalf("F5 Hasher key %d mismatch: got %d, present %v", i, result, ok)
				}
			}
			if table.count != 0 {
				b.Fatalf("F5 table retained %d entries", table.count)
			}
		}
	})
}

func TestF5HasherTableCollisionsAndCycles(t *testing.T) {
	table := newF5HashTable()
	values := [...]decimal.Decimal{decimal.MustParse("1.20"), decimal.MustParse("2.30"), decimal.MustParse("3.40")}
	cohorts := [...]decimal.Decimal{decimal.MustParse("1.200"), decimal.MustParse("2.300"), decimal.MustParse("3.400")}
	const forcedHash = uint64(7)
	for cycle := range 200 {
		if cycle > 0 && !table.nextCycle() {
			t.Fatal("table not empty at cycle boundary")
		}
		for i, value := range values {
			if !table.putAt(forcedHash, value, i) {
				t.Fatal("table refused colliding insertion")
			}
		}
		if !table.putAt(forcedHash, cohorts[1], 99) || table.count != 3 {
			t.Fatal("equal cohort did not update its existing slot")
		}
		for i, value := range cohorts {
			got, ok := table.getAt(forcedHash, value)
			want := i
			if i == 1 {
				want = 99
			}
			if !ok || got != want {
				t.Fatalf("collision lookup %d: got %d, present %v", i, got, ok)
			}
		}
		if !table.deleteAt(forcedHash, cohorts[0]) || !table.putAt(forcedHash, values[0], 0) || table.count != 3 {
			t.Fatal("deleted collision slot was not reusable")
		}
		for _, value := range cohorts {
			if !table.deleteAt(forcedHash, value) {
				t.Fatal("collision deletion lost an equal cohort")
			}
		}
		if table.count != 0 {
			t.Fatal("table retained entries after a full collision cycle")
		}
	}
}

var (
	sinkF5Bool    bool
	sinkF5Int     int
	sinkF5Decimal decimal.Decimal
	sinkF5Hash    uint64
)

// BenchmarkF5Methods isolates the public F5 methods around small and slow
// coefficients. These directed variants supplement the two matched 1024-key
// churn recipes; they are reported as their own rows.
func BenchmarkF5Methods(b *testing.B) {
	small := decimal.MustParse("123.4500")
	smallEqual := decimal.MustParse("123.45")
	smallOther := decimal.MustParse("123.46")
	large := decimal.MustParse("1234567890123456789012345678901234567890.00")
	largeEqual := decimal.MustParse("1234567890123456789012345678901234567890")
	largeOther := decimal.MustParse("1234567890123456789012345678901234567890.01")
	if !small.Equal(smallEqual) || small.Equal(smallOther) || small.Compare(smallOther) >= 0 ||
		!large.Equal(largeEqual) || large.Equal(largeOther) || large.Compare(largeOther) >= 0 {
		b.Fatal("F5 directed method inputs do not satisfy their checked relations")
	}
	if got := small.Reduce().String(); got != "123.45" {
		b.Fatalf("Reduce(123.4500) = %s", got)
	}
	if got := large.Reduce(); got.String() != "1.23456789012345678901234567890123456789E+39" || got.CoefficientDigits() != 39 {
		b.Fatalf("Reduce of the large operand = %s", got)
	}
	seed := maphash.MakeSeed()
	hasher := decimal.Hasher{}
	var h1, h2 maphash.Hash
	h1.SetSeed(seed)
	h2.SetSeed(seed)
	hasher.Hash(&h1, large)
	hasher.Hash(&h2, largeEqual)
	if h1.Sum64() != h2.Sum64() {
		b.Fatal("F5 equal large cohorts disagree under the same hash seed")
	}
	h1.Reset()
	h2.Reset()
	hasher.Hash(&h1, small)
	hasher.Hash(&h2, smallEqual)
	if h1.Sum64() != h2.Sum64() {
		b.Fatal("F5 equal small cohorts disagree under the same hash seed")
	}
	run := func(name string, operation func()) {
		b.Run("decimal/"+name, func(b *testing.B) {
			b.ReportAllocs()
			b.ResetTimer()
			for b.Loop() {
				operation()
			}
		})
	}
	run("equal-small-cohort", func() { sinkF5Bool = small.Equal(smallEqual) })
	run("equal-large-cohort", func() { sinkF5Bool = large.Equal(largeEqual) })
	run("equal-small-unequal", func() { sinkF5Bool = small.Equal(smallOther) })
	run("compare-small-unequal", func() { sinkF5Int = small.Compare(smallOther) })
	run("compare-large-unequal", func() { sinkF5Int = large.Compare(largeOther) })
	run("reduce-small", func() { sinkF5Decimal = small.Reduce() })
	run("reduce-large", func() { sinkF5Decimal = large.Reduce() })
	var h maphash.Hash
	h.SetSeed(seed)
	run("hash-small", func() {
		h.Reset()
		hasher.Hash(&h, small)
		sinkF5Hash = h.Sum64()
	})
	run("hash-large", func() {
		h.Reset()
		hasher.Hash(&h, large)
		sinkF5Hash = h.Sum64()
	})
}
