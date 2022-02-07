// Copyright 2021 Dolthub, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package val

import (
	"bytes"
	"encoding/binary"
	"math"
	"time"

	"github.com/shopspring/decimal"
)

type Type struct {
	Enc      Encoding
	Coll     Collation
	Nullable bool
}

type ByteSize uint16

const (
	int8Size    ByteSize = 1
	uint8Size   ByteSize = 1
	int16Size   ByteSize = 2
	uint16Size  ByteSize = 2
	int32Size   ByteSize = 4
	uint32Size  ByteSize = 4
	int48Size   ByteSize = 6
	uint48Size  ByteSize = 6
	int64Size   ByteSize = 8
	uint64Size  ByteSize = 8
	float32Size ByteSize = 4
	float64Size ByteSize = 8

	// todo(andy): experimental encoding
	timestampSize ByteSize = 15
)

type Collation uint16

const (
	ByteOrderCollation Collation = 0
)

type Encoding uint8

// Constant Size Encodings
const (
	NullEnc   Encoding = 0
	Int8Enc   Encoding = 1
	Uint8Enc  Encoding = 2
	Int16Enc  Encoding = 3
	Uint16Enc Encoding = 4
	// Int24Enc   Encoding = 5
	// Uint24Enc  Encoding = 6
	Int32Enc   Encoding = 7
	Uint32Enc  Encoding = 8
	Int64Enc   Encoding = 9
	Uint64Enc  Encoding = 10
	Float32Enc Encoding = 11
	Float64Enc Encoding = 12

	// todo(andy): experimental encodings
	//  consolidate into one
	TimestampEnc Encoding = 14
	DateEnc      Encoding = 15
	DatetimeEnc  Encoding = 16
	YearEnc      Encoding = 17

	sentinel Encoding = 127
)

// Variable Size Encodings
const (
	StringEnc Encoding = 128
	BytesEnc  Encoding = 129

	// todo(andy): experimental encodings
	DecimalEnc Encoding = 130
	JSONEnc    Encoding = 131
	TimeEnc    Encoding = 132

	// TODO
	//  BitEnc
	//  CharEnc
	//  VarCharEnc
	//  TextEnc
	//  BinaryEnc
	//  VarBinaryEnc
	//  BlobEnc
	//  JSONEnc
	//  EnumEnc
	//  SetEnc
	//  ExpressionEnc
	//  GeometryEnc
)

func sizeFromType(t Type) (ByteSize, bool) {
	switch t.Enc {
	case Int8Enc:
		return int8Size, true
	case Uint8Enc:
		return uint8Size, true
	case Int16Enc:
		return int16Size, true
	case Uint16Enc:
		return uint16Size, true
	case Int32Enc:
		return int32Size, true
	case Uint32Enc:
		return uint32Size, true
	case Int64Enc:
		return int64Size, true
	case Uint64Enc:
		return uint64Size, true
	case Float32Enc:
		return float32Size, true
	case Float64Enc:
		return float64Size, true
	case DateEnc, DatetimeEnc, TimestampEnc:
		return timestampSize, true
	case YearEnc:
		return int16Size, true
	default:
		return 0, false
	}
}

func ReadBool(val []byte) bool {
	expectSize(val, int8Size)
	return val[0] == 1
}
func ReadInt8(val []byte) int8 {
	expectSize(val, int8Size)
	return int8(val[0])
}

func ReadUint8(val []byte) uint8 {
	expectSize(val, uint8Size)
	return val[0]
}

func ReadInt16(val []byte) int16 {
	expectSize(val, int16Size)
	return int16(binary.LittleEndian.Uint16(val))
}

func ReadUint16(val []byte) uint16 {
	expectSize(val, uint16Size)
	return binary.LittleEndian.Uint16(val)
}

func ReadInt32(val []byte) int32 {
	expectSize(val, int32Size)
	return int32(binary.LittleEndian.Uint32(val))
}

func ReadUint32(val []byte) uint32 {
	expectSize(val, uint32Size)
	return binary.LittleEndian.Uint32(val)
}

func ReadUint48(val []byte) (u uint64) {
	expectSize(val, uint48Size)
	var tmp [8]byte
	// copy |val| to |tmp|
	tmp[5], tmp[4] = val[5], val[4]
	tmp[3], tmp[2] = val[3], val[2]
	tmp[1], tmp[0] = val[1], val[0]
	u = binary.LittleEndian.Uint64(tmp[:])
	return
}

func ReadInt64(val []byte) int64 {
	expectSize(val, int64Size)
	return int64(binary.LittleEndian.Uint64(val))
}

func ReadUint64(val []byte) uint64 {
	expectSize(val, uint64Size)
	return binary.LittleEndian.Uint64(val)
}

func ReadFloat32(val []byte) float32 {
	expectSize(val, float32Size)
	return math.Float32frombits(ReadUint32(val))
}

func ReadFloat64(val []byte) float64 {
	expectSize(val, float64Size)
	return math.Float64frombits(ReadUint64(val))
}

func ReadDecimal(val []byte) decimal.Decimal {
	// todo(andy): temporary lossy implementation
	//return decimal.NewFromFloat(ReadFloat64(val))
	return decimal.NewFromFloat(ReadFloat64(val))
}

func ReadTime(buf []byte) (t time.Time) {
	expectSize(buf, timestampSize)
	if err := t.UnmarshalBinary(buf); err != nil {
		panic(err)
	}
	return t
}

func ReadString(val []byte) string {
	// todo(andy): fix allocation
	return string(val)
}

func readBytes(val []byte) []byte {
	return val
}

func writeBool(buf []byte, val bool) {
	expectSize(buf, 1)
	if val {
		buf[0] = byte(1)
	} else {
		buf[0] = byte(0)
	}
}

func WriteInt8(buf []byte, val int8) {
	expectSize(buf, int8Size)
	buf[0] = byte(val)
}

func WriteUint8(buf []byte, val uint8) {
	expectSize(buf, uint8Size)
	buf[0] = byte(val)
}

func WriteInt16(buf []byte, val int16) {
	expectSize(buf, int16Size)
	binary.LittleEndian.PutUint16(buf, uint16(val))
}

func WriteUint16(buf []byte, val uint16) {
	expectSize(buf, uint16Size)
	binary.LittleEndian.PutUint16(buf, val)
}

func WriteInt32(buf []byte, val int32) {
	expectSize(buf, int32Size)
	binary.LittleEndian.PutUint32(buf, uint32(val))
}

func WriteUint32(buf []byte, val uint32) {
	expectSize(buf, uint32Size)
	binary.LittleEndian.PutUint32(buf, val)
}

func WriteUint48(buf []byte, u uint64) {
	const maxUint48 = uint64(1<<48 - 1)

	expectSize(buf, uint48Size)
	if u > maxUint48 {
		panic("uint is greater than max uint48")
	}
	var tmp [8]byte
	binary.LittleEndian.PutUint64(tmp[:], u)
	// copy |tmp| to |buf|
	buf[5], buf[4] = tmp[5], tmp[4]
	buf[3], buf[2] = tmp[3], tmp[2]
	buf[1], buf[0] = tmp[1], tmp[0]
}

func WriteInt64(buf []byte, val int64) {
	expectSize(buf, int64Size)
	binary.LittleEndian.PutUint64(buf, uint64(val))
}

func WriteUint64(buf []byte, val uint64) {
	expectSize(buf, uint64Size)
	binary.LittleEndian.PutUint64(buf, val)
}

func WriteFloat32(buf []byte, val float32) {
	expectSize(buf, float32Size)
	binary.LittleEndian.PutUint32(buf, math.Float32bits(val))
}

func WriteFloat64(buf []byte, val float64) {
	expectSize(buf, float64Size)
	binary.LittleEndian.PutUint64(buf, math.Float64bits(val))
}

func WriteTime(buf []byte, val time.Time) {
	expectSize(buf, timestampSize)
	// todo(andy): fix allocation here
	m, _ := val.MarshalBinary()
	copy(buf, m)
}

func writeString(buf []byte, val string, coll Collation) {
	expectSize(buf, ByteSize(len(val)))
	copy(buf, val)
}

func writeBytes(buf, val []byte, coll Collation) {
	expectSize(buf, ByteSize(len(val)))
	copy(buf, val)
}

func expectSize(buf []byte, sz ByteSize) {
	if ByteSize(len(buf)) != sz {
		panic("byte slice is not of expected size")
	}
}

func compare(typ Type, left, right []byte) int {
	// order NULLs last
	if left == nil {
		if right == nil {
			return 0
		} else {
			return 1
		}
	} else if right == nil {
		if left == nil {
			return 0
		} else {
			return -1
		}
	}

	switch typ.Enc {
	case Int8Enc:
		return compareInt8(ReadInt8(left), ReadInt8(right))
	case Uint8Enc:
		return compareUint8(ReadUint8(left), ReadUint8(right))
	case Int16Enc:
		return compareInt16(ReadInt16(left), ReadInt16(right))
	case Uint16Enc:
		return compareUint16(ReadUint16(left), ReadUint16(right))
	case Int32Enc:
		return compareInt32(ReadInt32(left), ReadInt32(right))
	case Uint32Enc:
		return compareUint32(ReadUint32(left), ReadUint32(right))
	case Int64Enc:
		return compareInt64(ReadInt64(left), ReadInt64(right))
	case Uint64Enc:
		return compareUint64(ReadUint64(left), ReadUint64(right))
	case Float32Enc:
		return compareFloat32(ReadFloat32(left), ReadFloat32(right))
	case Float64Enc:
		return compareFloat64(ReadFloat64(left), ReadFloat64(right))
	case YearEnc:
		return compareInt16(ReadInt16(left), ReadInt16(right))
	case DateEnc, DatetimeEnc, TimestampEnc:
		return compareTimestamp(ReadTime(left), ReadTime(right))
	case TimeEnc:
		panic("unimplemented")
	case DecimalEnc:
		// todo(andy): temporary Decimal implementation
		fallthrough
	case StringEnc:
		return compareString(ReadString(left), ReadString(right), typ.Coll)
	case BytesEnc:
		return compareBytes(readBytes(left), readBytes(right), typ.Coll)
	default:
		panic("unknown encoding")
	}
}

// false is less that true
func compareBool(l, r bool) int {
	if l == r {
		return 0
	}
	if !l && r {
		return -1
	}
	return 1
}

func compareInt8(l, r int8) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareUint8(l, r uint8) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareInt16(l, r int16) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareUint16(l, r uint16) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareInt32(l, r int32) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareUint32(l, r uint32) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareInt64(l, r int64) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareUint64(l, r uint64) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareFloat32(l, r float32) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareFloat64(l, r float64) int {
	if l == r {
		return 0
	} else if l < r {
		return -1
	} else {
		return 1
	}
}

func compareTimestamp(l, r time.Time) int {
	if l.Equal(r) {
		return 0
	}
	if l.Before(r) {
		return -1
	} else {
		return 1
	}
}

func compareString(l, r string, coll Collation) int {
	// todo(andy): collations
	return bytes.Compare([]byte(l), []byte(r))
}

func compareBytes(l, r []byte, coll Collation) int {
	// todo(andy): collations
	return bytes.Compare(l, r)
}

// rawCmp is an array of indexes used to perform raw Tuple comparisons.
// Under certain conditions, Tuple comparisons can be optimized by
// directly comparing Tuples as byte slices, rather than accessing
// and deserializing each field.
// If each of these conditions is met, raw comparisons can be used:
//   (1) All fields in the Tuple must be non-nullable.
//   (2) All fields in the Tuple must be of constant size
//  	  (eg Ints, Uints, Floats, Time types, etc.)
//
type rawCmp []int

var rawCmpLookup = map[Encoding]rawCmp{
	Int8Enc:   {0},
	Uint8Enc:  {0},
	Int16Enc:  {1, 0},
	Uint16Enc: {1, 0},
	Int32Enc:  {3, 2, 1, 0},
	Uint32Enc: {3, 2, 1, 0},
	Int64Enc:  {7, 6, 5, 4, 3, 2, 1, 0},
	Uint64Enc: {7, 6, 5, 4, 3, 2, 1, 0},
}

func compareRaw(left, right Tuple, mapping rawCmp) int {
	var l, r byte
	for _, idx := range mapping {
		l, r = left[idx], right[idx]
		if l != r {
			break
		}
	}
	if l > r {
		return 1
	} else if l < r {
		return -1
	}
	return 0
}

func maybeGetRawComparison(types ...Type) rawCmp {
	var raw []int
	offset := 0
	for _, typ := range types {
		if typ.Nullable {
			return nil
		}

		mapping, ok := rawCmpLookup[typ.Enc]
		if !ok {
			return nil
		}

		for i := range mapping {
			mapping[i] += offset
		}
		raw = append(raw, mapping...)
		offset += len(mapping)
	}
	return raw
}
