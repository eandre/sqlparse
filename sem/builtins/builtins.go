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
	"crypto/md5"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"fmt"
	"hash"
	"hash/crc32"
	"hash/fnv"
	"math"
	"regexp/syntax"
	"strings"
	"time"
	"unicode/utf8"

	"github.com/cockroachdb/apd"
	"github.com/eandre/sqlparse/pkg/util/json"
	"github.com/eandre/sqlparse/pkg/util/pgerror"
	"github.com/eandre/sqlparse/pkg/util/syncutil"
	"github.com/eandre/sqlparse/pkg/util/timeofday"
	"github.com/eandre/sqlparse/sem/tree"
	"github.com/eandre/sqlparse/sem/types"
	"github.com/pkg/errors"
)

var (
	errEmptyInputString = pgerror.NewError(pgerror.CodeInvalidParameterValueError, "the input string must not be empty")
	errAbsOfMinInt64    = pgerror.NewError(pgerror.CodeNumericValueOutOfRangeError, "abs of min integer value (-9223372036854775808) not defined")
	errSqrtOfNegNumber  = pgerror.NewError(pgerror.CodeInvalidArgumentForPowerFunctionError, "cannot take square root of a negative number")
	errLogOfNegNumber   = pgerror.NewError(pgerror.CodeInvalidArgumentForLogarithmError, "cannot take logarithm of a negative number")
	errLogOfZero        = pgerror.NewError(pgerror.CodeInvalidArgumentForLogarithmError, "cannot take logarithm of zero")
	errZeroIP           = pgerror.NewError(pgerror.CodeInvalidParameterValueError, "zero length IP")
	errChrValueTooSmall = pgerror.NewError(pgerror.CodeInvalidParameterValueError, "input value must be >= 0")
	errChrValueTooLarge = pgerror.NewErrorf(pgerror.CodeInvalidParameterValueError,
		"input value must be <= %d (maximum Unicode code point)", utf8.MaxRune)
)

const errInsufficientArgsFmtString = "unknown signature: %s()"

const (
	categoryComparison    = "Comparison"
	categoryCompatibility = "Compatibility"
	categoryDateAndTime   = "Date and time"
	categoryIDGeneration  = "ID generation"
	categorySequences     = "Sequence"
	categoryMath          = "Math and numeric"
	categoryString        = "String and byte"
	categoryArray         = "Array"
	categorySystemInfo    = "System info"
	categoryGenerator     = "Set-returning"
	categoryJSON          = "JSONB"
)

func categorizeType(t types.T) string {
	switch t {
	case types.Date, types.Interval, types.Timestamp, types.TimestampTZ:
		return categoryDateAndTime
	case types.Int, types.Decimal, types.Float:
		return categoryMath
	case types.String, types.Bytes:
		return categoryString
	default:
		return strings.ToUpper(t.String())
	}
}

var digitNames = []string{"zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"}

// builtinDefinition represents a built-in function before it becomes
// a tree.FunctionDefinition.
type builtinDefinition struct {
	props     tree.FunctionProperties
	overloads []tree.Overload
}

// GetBuiltinProperties provides low-level access to a built-in function's properties.
// For a better, semantic-rich interface consider using tree.FunctionDefinition
// instead, and resolve function names via ResolvableFunctionReference.Resolve().
func GetBuiltinProperties(name string) (*tree.FunctionProperties, []tree.Overload) {
	def, ok := builtins[name]
	if !ok {
		return nil, nil
	}
	return &def.props, def.overloads
}

// defProps is used below to define built-in functions with default properties.
func defProps() tree.FunctionProperties { return tree.FunctionProperties{} }

// arrayProps is used below for array functions.
func arrayProps() tree.FunctionProperties { return tree.FunctionProperties{Category: categoryArray} }

// arrayPropsNullableArgs is used below for array functions that accept NULLs as arguments.
func arrayPropsNullableArgs() tree.FunctionProperties {
	p := arrayProps()
	p.NullableArgs = true
	return p
}

func makeBuiltin(props tree.FunctionProperties, overloads ...tree.Overload) builtinDefinition {
	return builtinDefinition{
		props:     props,
		overloads: overloads,
	}
}

func newDecodeError(enc string) error {
	return pgerror.NewErrorf(pgerror.CodeCharacterNotInRepertoireError,
		"invalid byte sequence for encoding %q", enc)
}

func newEncodeError(c rune, enc string) error {
	return pgerror.NewErrorf(pgerror.CodeUntranslatableCharacterError,
		"character %q has no representation in encoding %q", c, enc)
}

// builtins contains the built-in functions indexed by name.
//
// For use in other packages, see AllBuiltinNames and GetBuiltinProperties().
var builtins = map[string]builtinDefinition{
	// TODO(XisiHuang): support encoding, i.e., length(str, encoding).
	"length":           lengthImpls,
	"char_length":      lengthImpls,
	"character_length": lengthImpls,

	"bit_length": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		stringOverload1(types.Int, "Calculates the number of bits used to represent `val`."),
		bytesOverload1(types.Int, "Calculates the number of bits in `val`."),
	),

	"octet_length": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		stringOverload1(types.Int, "Calculates the number of bytes used to represent `val`."),
		bytesOverload1(types.Int, "Calculates the number of bytes in `val`."),
	),

	// TODO(pmattis): What string functions should also support types.Bytes?

	"lower": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		stringOverload1(types.String, "Converts all characters in `val` to their lower-case equivalents.")),

	"upper": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		stringOverload1(types.String, "Converts all characters in `val` to their to their upper-case equivalents.")),

	"substr":    substringImpls,
	"substring": substringImpls,

	// concat concatenates the text representations of all the arguments.
	// NULL arguments are ignored.
	"concat": makeBuiltin(tree.FunctionProperties{NullableArgs: true},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.String},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Concatenates a comma-separated list of strings.",
		},
	),

	"concat_ws": makeBuiltin(tree.FunctionProperties{NullableArgs: true},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.String},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Uses the first argument as a separator between the concatenation of the " +
				"subsequent arguments. \n\nFor example `concat_ws('!','wow','great')` " +
				"returns `wow!great`.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-string.html#FUNCTIONS-STRING-OTHER
	"convert_from": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"str", types.Bytes}, {"enc", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Decode the bytes in `str` into a string using encoding `enc`. " +
				"Supports encodings 'UTF8' and 'LATIN1'.",
		}),

	// https://www.postgresql.org/docs/10/static/functions-string.html#FUNCTIONS-STRING-OTHER
	"convert_to": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"str", types.String}, {"enc", types.String}},
			ReturnType: tree.FixedReturnType(types.Bytes),
			Info: "Encode the string `str` as a byte array using encoding `enc`. " +
				"Supports encodings 'UTF8' and 'LATIN1'.",
		}),

	"gen_random_uuid": makeBuiltin(
		tree.FunctionProperties{
			Category: categoryIDGeneration,
			Impure:   true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.UUID),
			Info:       "Generates a random UUID and returns it as a value of UUID type.",
		},
	),

	"to_uuid": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.String}},
			ReturnType: tree.FixedReturnType(types.Bytes),
			Info: "Converts the character string representation of a UUID to its byte string " +
				"representation.",
		},
	),

	"from_uuid": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Bytes}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Converts the byte string representation of a UUID to its character string " +
				"representation.",
		},
	),

	// The following functions are all part of the NET address functions. They can
	// be found in the postgres reference at https://www.postgresql.org/docs/9.6/static/functions-net.html#CIDR-INET-FUNCTIONS-TABLE
	// This includes:
	// - abbrev
	// - broadcast
	// - family
	// - host
	// - hostmask
	// - masklen
	// - netmask
	// - set_masklen
	// - text(inet)
	// - inet_same_family

	"abbrev": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Converts the combined IP address and prefix length to an abbreviated display format as text." +
				"For INET types, this will omit the prefix length if it's not the default (32 or IPv4, 128 for IPv6)" +
				"\n\nFor example, `abbrev('192.168.1.2/24')` returns `'192.168.1.2/24'`",
		},
	),

	"broadcast": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.INet),
			Info: "Gets the broadcast address for the network address represented by the value." +
				"\n\nFor example, `broadcast('192.168.1.2/24')` returns `'192.168.1.255/24'`",
		},
	),

	"family": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Extracts the IP family of the value; 4 for IPv4, 6 for IPv6." +
				"\n\nFor example, `family('::1')` returns `6`",
		},
	),

	"host": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Extracts the address part of the combined address/prefixlen value as text." +
				"\n\nFor example, `host('192.168.1.2/16')` returns `'192.168.1.2'`",
		},
	),

	"hostmask": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.INet),
			Info: "Creates an IP host mask corresponding to the prefix length in the value." +
				"\n\nFor example, `hostmask('192.168.1.2/16')` returns `'0.0.255.255'`",
		},
	),

	"masklen": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Retrieves the prefix length stored in the value." +
				"\n\nFor example, `masklen('192.168.1.2/16')` returns `16`",
		},
	),

	"netmask": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.INet),
			Info: "Creates an IP network mask corresponding to the prefix length in the value." +
				"\n\nFor example, `netmask('192.168.1.2/16')` returns `'255.255.0.0'`",
		},
	),

	"set_masklen": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"val", types.INet},
				{"prefixlen", types.Int},
			},
			ReturnType: tree.FixedReturnType(types.INet),
			Info: "Sets the prefix length of `val` to `prefixlen`.\n\n" +
				"For example, `set_masklen('192.168.1.2', 16)` returns `'192.168.1.2/16'`.",
		},
	),

	"text": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.INet}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Converts the IP address and prefix length to text.",
		},
	),

	"inet_same_family": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"val", types.INet},
				{"val", types.INet},
			},
			ReturnType: tree.FixedReturnType(types.Bool),
			Info:       "Checks if two IP addresses are of the same IP family.",
		},
	),

	"inet_contained_by_or_equals": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"val", types.INet},
				{"container", types.INet},
			},
			ReturnType: tree.FixedReturnType(types.Bool),
			Info: "Test for subnet inclusion or equality, using only the network parts of the addresses. " +
				"The host part of the addresses is ignored.",
		},
	),

	"inet_contains_or_contained_by": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"val", types.INet},
				{"val", types.INet},
			},
			ReturnType: tree.FixedReturnType(types.Bool),
			Info: "Test for subnet inclusion, using only the network parts of the addresses. " +
				"The host part of the addresses is ignored.",
		},
	),

	"inet_contains_or_equals": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"container", types.INet},
				{"val", types.INet},
			},
			ReturnType: tree.FixedReturnType(types.Bool),
			Info: "Test for subnet inclusion or equality, using only the network parts of the addresses. " +
				"The host part of the addresses is ignored.",
		},
	),

	"from_ip": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Bytes}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Converts the byte string representation of an IP to its character string " +
				"representation.",
		},
	),

	"to_ip": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.String}},
			ReturnType: tree.FixedReturnType(types.Bytes),
			Info: "Converts the character string representation of an IP to its byte string " +
				"representation.",
		},
	),

	"split_part": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"input", types.String},
				{"delimiter", types.String},
				{"return_index_pos", types.Int},
			},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Splits `input` on `delimiter` and return the value in the `return_index_pos`  " +
				"position (starting at 1). \n\nFor example, `split_part('123.456.789.0','.',3)`" +
				"returns `789`.",
		},
	),

	"repeat": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.String}, {"repeat_counter", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Concatenates `input` `repeat_counter` number of times.\n\nFor example, " +
				"`repeat('dog', 2)` returns `dogdog`.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-binarystring.html
	"encode": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"data", types.Bytes}, {"format", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Encodes `data` using `format` (`hex` / `escape` / `base64`).",
		},
	),

	"decode": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"text", types.String}, {"format", types.String}},
			ReturnType: tree.FixedReturnType(types.Bytes),
			Info:       "Decodes `data` using `format` (`hex` / `escape` / `base64`).",
		},
	),

	"ascii": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		stringOverload1(types.Int, "Returns the character code of the first character in `val`. Despite the name, the function supports Unicode too.")),

	"chr": makeBuiltin(tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the character with the code given in `val`. Inverse function of `ascii()`.",
		},
	),

	"md5": hashBuiltin(
		func() hash.Hash { return md5.New() },
		"Calculates the MD5 hash value of a set of values.",
	),

	"sha1": hashBuiltin(
		func() hash.Hash { return sha1.New() },
		"Calculates the SHA1 hash value of a set of values.",
	),

	"sha256": hashBuiltin(
		func() hash.Hash { return sha256.New() },
		"Calculates the SHA256 hash value of a set of values.",
	),

	"sha512": hashBuiltin(
		func() hash.Hash { return sha512.New() },
		"Calculates the SHA512 hash value of a set of values.",
	),

	"fnv32": hash32Builtin(
		func() hash.Hash32 { return fnv.New32() },
		"Calculates the 32-bit FNV-1 hash value of a set of values.",
	),

	"fnv32a": hash32Builtin(
		func() hash.Hash32 { return fnv.New32a() },
		"Calculates the 32-bit FNV-1a hash value of a set of values.",
	),

	"fnv64": hash64Builtin(
		func() hash.Hash64 { return fnv.New64() },
		"Calculates the 64-bit FNV-1 hash value of a set of values.",
	),

	"fnv64a": hash64Builtin(
		func() hash.Hash64 { return fnv.New64a() },
		"Calculates the 64-bit FNV-1a hash value of a set of values.",
	),

	"crc32ieee": hash32Builtin(
		func() hash.Hash32 { return crc32.New(crc32.IEEETable) },
		"Calculates the CRC-32 hash using the IEEE polynomial.",
	),

	"crc32c": hash32Builtin(
		func() hash.Hash32 { return crc32.New(crc32.MakeTable(crc32.Castagnoli)) },
		"Calculates the CRC-32 hash using the Castagnoli polynomial.",
	),

	"to_hex": makeBuiltin(
		tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Converts `val` to its hexadecimal representation.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Bytes}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Converts `val` to its hexadecimal representation.",
		},
	),

	"to_english": makeBuiltin(
		tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "This function enunciates the value of its argument using English cardinals.",
		},
	),

	// The SQL parser coerces POSITION to STRPOS.
	"strpos": makeBuiltin(
		tree.FunctionProperties{Category: categoryString},
		stringOverload2("input", "find", types.Int, "Calculates the position where the string `find` begins in `input`. \n\nFor"+
			" example, `strpos('doggie', 'gie')` returns `4`.")),

	"overlay": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"input", types.String},
				{"overlay_val", types.String},
				{"start_pos", types.Int},
			},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Replaces characters in `input` with `overlay_val` starting at `start_pos` " +
				"(begins at 1). \n\nFor example, `overlay('doggie', 'CAT', 2)` returns " +
				"`dCATie`.",
		},
		tree.Overload{
			Types: tree.ArgTypes{
				{"input", types.String},
				{"overlay_val", types.String},
				{"start_pos", types.Int},
				{"end_pos", types.Int},
			},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Deletes the characters in `input` between `start_pos` and `end_pos` (count " +
				"starts at 1), and then insert `overlay_val` at `start_pos`.",
		},
	),

	"lpad": makeBuiltin(
		tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"string", types.String}, {"length", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Pads `string` to `length` by adding ' ' to the left of `string`." +
				"If `string` is longer than `length` it is truncated.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"string", types.String}, {"length", types.Int}, {"fill", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Pads `string` by adding `fill` to the left of `string` to make it `length`. " +
				"If `string` is longer than `length` it is truncated.",
		},
	),

	"rpad": makeBuiltin(
		tree.FunctionProperties{Category: categoryString},
		tree.Overload{
			Types:      tree.ArgTypes{{"string", types.String}, {"length", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Pads `string` to `length` by adding ' ' to the right of string. " +
				"If `string` is longer than `length` it is truncated.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"string", types.String}, {"length", types.Int}, {"fill", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Pads `string` to `length` by adding `fill` to the right of `string`. " +
				"If `string` is longer than `length` it is truncated.",
		},
	),

	// The SQL parser coerces TRIM(...) and TRIM(BOTH ...) to BTRIM(...).
	"btrim": makeBuiltin(defProps(),
		stringOverload2("input", "trim_chars", types.String, "Removes any characters included in `trim_chars` from the beginning or end"+
			" of `input` (applies recursively). \n\nFor example, `btrim('doggie', 'eod')` "+
			"returns `ggi`."),
		stringOverload1(types.String, "Removes all spaces from the beginning and end of `val`."),
	),

	// The SQL parser coerces TRIM(LEADING ...) to LTRIM(...).
	"ltrim": makeBuiltin(defProps(),
		stringOverload2("input", "trim_chars", types.String, "Removes any characters included in `trim_chars` from the beginning "+
			"(left-hand side) of `input` (applies recursively). \n\nFor example, "+
			"`ltrim('doggie', 'od')` returns `ggie`."),
		stringOverload1(types.String, "Removes all spaces from the beginning (left-hand side) of `val`."),
	),

	// The SQL parser coerces TRIM(TRAILING ...) to RTRIM(...).
	"rtrim": makeBuiltin(defProps(),
		stringOverload2("input", "trim_chars", types.String, "Removes any characters included in `trim_chars` from the end (right-hand "+
			"side) of `input` (applies recursively). \n\nFor example, `rtrim('doggie', 'ei')` "+
			"returns `dogg`."),
		stringOverload1(types.String, "Removes all spaces from the end (right-hand side) of `val`."),
	),

	"reverse": makeBuiltin(defProps(),
		stringOverload1(types.String, "Reverses the order of the string's characters.")),

	"replace": makeBuiltin(defProps(),
		stringOverload3("input", "find", "replace",
			types.String,
			"Replaces all occurrences of `find` with `replace` in `input`",
		)),

	"translate": makeBuiltin(defProps(),
		stringOverload3("input", "find", "replace",
			types.String, "In `input`, replaces the first character from `find` with the first "+
				"character in `replace`; repeat for each character in `find`. \n\nFor example, "+
				"`translate('doggie', 'dog', '123');` returns `1233ie`.")),

	"regexp_extract": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.String}, {"regex", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the first match for the Regular Expression `regex` in `input`.",
		},
	),

	"regexp_replace": makeBuiltin(defProps(),
		tree.Overload{
			Types: tree.ArgTypes{
				{"input", types.String},
				{"regex", types.String},
				{"replace", types.String},
			},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Replaces matches for the Regular Expression `regex` in `input` with the " +
				"Regular Expression `replace`.",
		},
		tree.Overload{
			Types: tree.ArgTypes{
				{"input", types.String},
				{"regex", types.String},
				{"replace", types.String},
				{"flags", types.String},
			},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Replaces matches for the regular expression `regex` in `input` with the regular " +
				"expression `replace` using `flags`." + `

CockroachDB supports the following flags:

| Flag           | Description                                                       |
|----------------|-------------------------------------------------------------------|
| **c**          | Case-sensitive matching                                           |
| **g**          | Global matching (match each substring instead of only the first)  |
| **i**          | Case-insensitive matching                                         |
| **m** or **n** | Newline-sensitive (see below)                                     |
| **p**          | Partial newline-sensitive matching (see below)                    |
| **s**          | Newline-insensitive (default)                                     |
| **w**          | Inverse partial newline-sensitive matching (see below)            |

| Mode | ` + "`.` and `[^...]` match newlines | `^` and `$` match line boundaries" + `|
|------|----------------------------------|--------------------------------------|
| s    | yes                              | no                                   |
| w    | yes                              | yes                                  |
| p    | no                               | no                                   |
| m/n  | no                               | yes                                  |`,
		},
	),

	"like_escape": makeBuiltin(defProps(),
		stringOverload3(
			"unescaped", "pattern", "escape",
			types.Bool,
			"Matches `unescaped` with `pattern` using 'escape' as an escape token.",
		)),

	"not_like_escape": makeBuiltin(defProps(),
		stringOverload3(
			"unescaped", "pattern", "escape",
			types.Bool,
			"Checks whether `unescaped` not matches with `pattern` using 'escape' as an escape token.",
		)),

	"ilike_escape": makeBuiltin(defProps(),
		stringOverload3(
			"unescaped", "pattern", "escape",
			types.Bool,
			"Matches case insensetively `unescaped` with `pattern` using 'escape' as an escape token.",
		)),

	"not_ilike_escape": makeBuiltin(defProps(),
		stringOverload3(
			"unescaped", "pattern", "escape",
			types.Bool,
			"Checks whether `unescaped` not matches case insensetively with `pattern` using 'escape' as an escape token.",
		)),

	"similar_to_escape": makeBuiltin(defProps(),
		stringOverload3(
			"unescaped", "pattern", "escape",
			types.Bool,
			"Matches `unescaped` with `pattern` using 'escape' as an escape token.",
		)),

	"not_similar_to_escape": makeBuiltin(defProps(),
		stringOverload3(
			"unescaped", "pattern", "escape",
			types.Bool,
			"Checks whether `unescaped` not matches with `pattern` using 'escape' as an escape token.",
		)),

	"initcap": makeBuiltin(defProps(),
		stringOverload1(types.String, "Capitalizes the first letter of `val`.")),

	"quote_ident": makeBuiltin(defProps(),
		stringOverload1(types.String, "Return `val` suitably quoted to serve as identifier in a SQL statement.")),

	"quote_literal": makeBuiltin(defProps(),
		tree.Overload{
			Types:             tree.ArgTypes{{"val", types.String}},
			ReturnType:        tree.FixedReturnType(types.String),
			PreferredOverload: true,
			Info:              "Return `val` suitably quoted to serve as string literal in a SQL statement.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Any}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Coerce `val` to a string and then quote it as a literal.",
		},
	),

	// quote_nullable is the same as quote_literal but accepts NULL arguments.
	"quote_nullable": makeBuiltin(
		tree.FunctionProperties{
			Category:     categoryString,
			NullableArgs: true,
		},
		tree.Overload{
			Types:             tree.ArgTypes{{"val", types.String}},
			ReturnType:        tree.FixedReturnType(types.String),
			PreferredOverload: true,
			Info:              "Coerce `val` to a string and then quote it as a literal. If `val` is NULL, returns 'NULL'.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Any}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Coerce `val` to a string and then quote it as a literal. If `val` is NULL, returns 'NULL'.",
		},
	),

	"left": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.Bytes}, {"return_set", types.Int}},
			ReturnType: tree.FixedReturnType(types.Bytes),
			Info:       "Returns the first `return_set` bytes from `input`.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.String}, {"return_set", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the first `return_set` characters from `input`.",
		},
	),

	"right": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.Bytes}, {"return_set", types.Int}},
			ReturnType: tree.FixedReturnType(types.Bytes),
			Info:       "Returns the last `return_set` bytes from `input`.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.String}, {"return_set", types.Int}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the last `return_set` characters from `input`.",
		},
	),

	"random": makeBuiltin(
		tree.FunctionProperties{
			Impure:                  true,
			NeedsRepeatedEvaluation: true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Float),
			Info:       "Returns a random float between 0 and 1.",
		},
	),

	"unique_rowid": makeBuiltin(
		tree.FunctionProperties{
			Category: categoryIDGeneration,
			Impure:   true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Returns a unique ID used by CockroachDB to generate unique row IDs if a " +
				"Primary Key isn't defined for the table. The value is a combination of the " +
				"insert timestamp and the ID of the node executing the statement, which " +
				"guarantees this combination is globally unique. However, there can be " +
				"gaps and the order is not completely guaranteed.",
		},
	),

	// Sequence functions.

	"nextval": makeBuiltin(
		tree.FunctionProperties{
			Category:         categorySequences,
			DistsqlBlacklist: true,
			Impure:           true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"sequence_name", types.String}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Advances the given sequence and returns its new value.",
		},
	),

	"currval": makeBuiltin(
		tree.FunctionProperties{
			Category:         categorySequences,
			DistsqlBlacklist: true,
			Impure:           true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"sequence_name", types.String}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Returns the latest value obtained with nextval for this sequence in this session.",
		},
	),

	"lastval": makeBuiltin(
		tree.FunctionProperties{
			Category: categorySequences,
			Impure:   true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Return value most recently obtained with nextval in this session.",
		},
	),

	// Note: behavior is slightly different than Postgres for performance reasons.
	// See https://github.com/cockroachdb/cockroach/issues/21564
	"setval": makeBuiltin(
		tree.FunctionProperties{
			Category:         categorySequences,
			DistsqlBlacklist: true,
			Impure:           true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"sequence_name", types.String}, {"value", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Set the given sequence's current value. The next call to nextval will return " +
				"`value + Increment`",
		},
		tree.Overload{
			Types: tree.ArgTypes{
				{"sequence_name", types.String}, {"value", types.Int}, {"is_called", types.Bool},
			},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Set the given sequence's current value. If is_called is false, the next call to " +
				"nextval will return `value`; otherwise `value + Increment`.",
		},
	),

	"experimental_uuid_v4": uuidV4Impl,
	"uuid_v4":              uuidV4Impl,

	"greatest": makeBuiltin(
		tree.FunctionProperties{
			Category:     categoryComparison,
			NullableArgs: true,
		},
		tree.Overload{
			Types:      tree.HomogeneousType{},
			ReturnType: tree.FirstNonNullReturnType(),
			Info:       "Returns the element with the greatest value.",
		},
	),

	"least": makeBuiltin(
		tree.FunctionProperties{
			Category:     categoryComparison,
			NullableArgs: true,
		},
		tree.Overload{
			Types:      tree.HomogeneousType{},
			ReturnType: tree.FirstNonNullReturnType(),
			Info:       "Returns the element with the lowest value.",
		},
	),

	// Timestamp/Date functions.

	// https://www.postgresql.org/docs/10/static/functions-datetime.html
	"age": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.TimestampTZ}},
			ReturnType: tree.FixedReturnType(types.Interval),
			Info:       "Calculates the interval between `val` and the current time.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"end", types.TimestampTZ}, {"begin", types.TimestampTZ}},
			ReturnType: tree.FixedReturnType(types.Interval),
			Info:       "Calculates the interval between `begin` and `end`.",
		},
	),

	"current_date": makeBuiltin(
		tree.FunctionProperties{Impure: true},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Date),
			Info:       "Returns the date of the current transaction." + txnTSContextDoc,
		},
	),

	"now":                   txnTSImpl,
	"current_timestamp":     txnTSImpl,
	"transaction_timestamp": txnTSImpl,

	"statement_timestamp": makeBuiltin(
		tree.FunctionProperties{Impure: true},
		tree.Overload{
			Types:             tree.ArgTypes{},
			ReturnType:        tree.FixedReturnType(types.TimestampTZ),
			PreferredOverload: true,
			Info:              "Returns the start time of the current statement.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Timestamp),
			Info:       "Returns the start time of the current statement.",
		},
	),

	"cluster_logical_timestamp": makeBuiltin(
		tree.FunctionProperties{
			Category: categorySystemInfo,
			Impure:   true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Decimal),
			Info: `Returns the logical time of the current transaction.

This function is reserved for testing purposes by CockroachDB
developers and its definition may change without prior notice.

Note that uses of this function disable server-side optimizations and
may increase either contention or retry errors, or both.`,
		},
	),

	"clock_timestamp": makeBuiltin(
		tree.FunctionProperties{Impure: true},
		tree.Overload{
			Types:             tree.ArgTypes{},
			ReturnType:        tree.FixedReturnType(types.TimestampTZ),
			PreferredOverload: true,
			Info:              "Returns the current system time on one of the cluster nodes.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Timestamp),
			Info:       "Returns the current system time on one of the cluster nodes.",
		},
	),

	"extract": makeBuiltin(
		tree.FunctionProperties{Category: categoryDateAndTime},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Timestamp}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Extracts `element` from `input`.\n\n" +
				"Compatible elements: year, quarter, month, week, dayofweek, dayofyear,\n" +
				"hour, minute, second, millisecond, microsecond, epoch",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Date}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Extracts `element` from `input`.\n\n" +
				"Compatible elements: year, quarter, month, week, dayofweek, dayofyear,\n" +
				"hour, minute, second, millisecond, microsecond, epoch",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.TimestampTZ}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Extracts `element` from `input`.\n\n" +
				"Compatible elements: year, quarter, month, week, dayofweek, dayofyear,\n" +
				"hour, minute, second, millisecond, microsecond, epoch",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Time}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Extracts `element` from `input`.\n\n" +
				"Compatible elements: hour, minute, second, millisecond, microsecond, epoch",
		},
	),

	"extract_duration": makeBuiltin(
		tree.FunctionProperties{Category: categoryDateAndTime},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Interval}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Extracts `element` from `input`.\n" +
				"Compatible elements: hour, minute, second, millisecond, microsecond.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-datetime.html#FUNCTIONS-DATETIME-TRUNC
	//
	// PostgreSQL documents date_trunc for timestamp, timestamptz and
	// interval. It will also handle date and time inputs by casting them,
	// so we support those for compatibility. This gives us the following
	// function signatures:
	//
	//  date_trunc(string, time)        -> interval
	//  date_trunc(string, date)        -> timestamptz
	//  date_trunc(string, timestamp)   -> timestamp
	//  date_trunc(string, timestamptz) -> timestamptz
	//
	// See the following snippet from running the functions in PostgreSQL:
	//
	// 		postgres=# select pg_typeof(date_trunc('month', '2017-04-11 00:00:00'::timestamp));
	// 							pg_typeof
	// 		-----------------------------
	// 		timestamp without time zone
	//
	// 		postgres=# select pg_typeof(date_trunc('month', '2017-04-11 00:00:00'::date));
	// 						pg_typeof
	// 		--------------------------
	// 		timestamp with time zone
	//
	// 		postgres=# select pg_typeof(date_trunc('month', '2017-04-11 00:00:00'::time));
	// 		pg_typeof
	// 		-----------
	// 		interval
	//
	// This implicit casting behavior is mentioned in the PostgreSQL documentation:
	// https://www.postgresql.org/docs/10/static/functions-datetime.html
	// > source is a value expression of type timestamp or interval. (Values
	// > of type date and time are cast automatically to timestamp or interval,
	// > respectively.)
	//
	"date_trunc": makeBuiltin(
		tree.FunctionProperties{Category: categoryDateAndTime},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Timestamp}},
			ReturnType: tree.FixedReturnType(types.Timestamp),
			Info: "Truncates `input` to precision `element`.  Sets all fields that are less\n" +
				"significant than `element` to zero (or one, for day and month)\n\n" +
				"Compatible elements: year, quarter, month, week, hour, minute, second,\n" +
				"millisecond, microsecond.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Date}},
			ReturnType: tree.FixedReturnType(types.TimestampTZ),
			Info: "Truncates `input` to precision `element`.  Sets all fields that are less\n" +
				"significant than `element` to zero (or one, for day and month)\n\n" +
				"Compatible elements: year, quarter, month, week, hour, minute, second,\n" +
				"millisecond, microsecond.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.Time}},
			ReturnType: tree.FixedReturnType(types.Interval),
			Info: "Truncates `input` to precision `element`.  Sets all fields that are less\n" +
				"significant than `element` to zero.\n\n" +
				"Compatible elements: hour, minute, second, millisecond, microsecond.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"element", types.String}, {"input", types.TimestampTZ}},
			ReturnType: tree.FixedReturnType(types.TimestampTZ),
			Info: "Truncates `input` to precision `element`.  Sets all fields that are less\n" +
				"significant than `element` to zero (or one, for day and month)\n\n" +
				"Compatible elements: year, quarter, month, week, hour, minute, second,\n" +
				"millisecond, microsecond.",
		},
	),

	// Math functions
	"abs": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Abs(x))), nil
		}, "Calculates the absolute value of `val`."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			dd := &tree.DDecimal{}
			dd.Abs(x)
			return dd, nil
		}, "Calculates the absolute value of `val`."),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Calculates the absolute value of `val`.",
		},
	),

	"acos": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Acos(x))), nil
		}, "Calculates the inverse cosine of `val`."),
	),

	"asin": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Asin(x))), nil
		}, "Calculates the inverse sine of `val`."),
	),

	"atan": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Atan(x))), nil
		}, "Calculates the inverse tangent of `val`."),
	),

	"atan2": makeBuiltin(defProps(),
		floatOverload2("x", "y", func(x, y float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Atan2(x, y))), nil
		}, "Calculates the inverse tangent of `x`/`y`."),
	),

	"cbrt": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Cbrt(x))), nil
		}, "Calculates the cube root (∛) of `val`."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			dd := &tree.DDecimal{}
			_, err := tree.DecimalCtx.Cbrt(&dd.Decimal, x)
			return dd, err
		}, "Calculates the cube root (∛) of `val`."),
	),

	"ceil":    ceilImpl,
	"ceiling": ceilImpl,

	"cos": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Cos(x))), nil
		}, "Calculates the cosine of `val`."),
	),

	"cot": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(1 / math.Tan(x))), nil
		}, "Calculates the cotangent of `val`."),
	),

	"degrees": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(180.0 * x / math.Pi)), nil
		}, "Converts `val` as a radian value to a degree value."),
	),

	"div": makeBuiltin(defProps(),
		floatOverload2("x", "y", func(x, y float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Trunc(x / y))), nil
		}, "Calculates the integer quotient of `x`/`y`."),
		decimalOverload2("x", "y", func(x, y *apd.Decimal) (tree.Datum, error) {
			if y.Sign() == 0 {
				return nil, tree.ErrDivByZero
			}
			dd := &tree.DDecimal{}
			_, err := tree.HighPrecisionCtx.QuoInteger(&dd.Decimal, x, y)
			return dd, err
		}, "Calculates the integer quotient of `x`/`y`."),
		tree.Overload{
			Types:      tree.ArgTypes{{"x", types.Int}, {"y", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Calculates the integer quotient of `x`/`y`.",
		},
	),

	"exp": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Exp(x))), nil
		}, "Calculates *e* ^ `val`."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			dd := &tree.DDecimal{}
			_, err := tree.DecimalCtx.Exp(&dd.Decimal, x)
			return dd, err
		}, "Calculates *e* ^ `val`."),
	),

	"floor": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Floor(x))), nil
		}, "Calculates the largest integer not greater than `val`."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			dd := &tree.DDecimal{}
			_, err := tree.ExactCtx.Floor(&dd.Decimal, x)
			return dd, err
		}, "Calculates the largest integer not greater than `val`."),
	),

	"isnan": makeBuiltin(defProps(),
		tree.Overload{
			// Can't use floatBuiltin1 here because this one returns
			// a boolean.
			Types:      tree.ArgTypes{{"val", types.Float}},
			ReturnType: tree.FixedReturnType(types.Bool),
			Info:       "Returns true if `val` is NaN, false otherwise.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Decimal}},
			ReturnType: tree.FixedReturnType(types.Bool),
			Info:       "Returns true if `val` is NaN, false otherwise.",
		},
	),

	"ln": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Log(x))), nil
		}, "Calculates the natural log of `val`."),
		decimalLogFn(tree.DecimalCtx.Ln, "Calculates the natural log of `val`."),
	),

	"log": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Log10(x))), nil
		}, "Calculates the base 10 log of `val`."),
		decimalLogFn(tree.DecimalCtx.Log10, "Calculates the base 10 log of `val`."),
	),

	"mod": makeBuiltin(defProps(),
		floatOverload2("x", "y", func(x, y float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Mod(x, y))), nil
		}, "Calculates `x`%`y`."),
		decimalOverload2("x", "y", func(x, y *apd.Decimal) (tree.Datum, error) {
			if y.Sign() == 0 {
				return nil, tree.ErrZeroModulus
			}
			dd := &tree.DDecimal{}
			_, err := tree.HighPrecisionCtx.Rem(&dd.Decimal, x, y)
			return dd, err
		}, "Calculates `x`%`y`."),
		tree.Overload{
			Types:      tree.ArgTypes{{"x", types.Int}, {"y", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Calculates `x`%`y`.",
		},
	),

	"pi": makeBuiltin(defProps(),
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.Float),
			Info:       "Returns the value for pi (3.141592653589793).",
		},
	),

	"pow":   powImpls,
	"power": powImpls,

	"radians": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(x * math.Pi / 180.0)), nil
		}, "Converts `val` as a degree value to a radians value."),
	),

	"round": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.RoundToEven(x))), nil
		}, "Rounds `val` to the nearest integer using half to even (banker's) rounding."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			return roundDecimal(x, 0)
		}, "Rounds `val` to the nearest integer, half away from zero: "+
			"round(+/-2.4) = +/-2, round(+/-2.5) = +/-3."),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.Float}, {"decimal_accuracy", types.Int}},
			ReturnType: tree.FixedReturnType(types.Float),
			Info: "Keeps `decimal_accuracy` number of figures to the right of the zero position " +
				" in `input` using half to even (banker's) rounding.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.Decimal}, {"decimal_accuracy", types.Int}},
			ReturnType: tree.FixedReturnType(types.Decimal),
			Info: "Keeps `decimal_accuracy` number of figures to the right of the zero position " +
				"in `input` using half away from zero rounding. If `decimal_accuracy` " +
				"is not in the range -2^31...(2^31-1), the results are undefined.",
		},
	),

	"sin": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Sin(x))), nil
		}, "Calculates the sine of `val`."),
	),

	"sign": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			switch {
			case x < 0:
				return tree.NewDFloat(-1), nil
			case x == 0:
				return tree.NewDFloat(0), nil
			}
			return tree.NewDFloat(1), nil
		}, "Determines the sign of `val`: **1** for positive; **0** for 0 values; **-1** for "+
			"negative."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			d := &tree.DDecimal{}
			d.Decimal.SetFinite(int64(x.Sign()), 0)
			return d, nil
		}, "Determines the sign of `val`: **1** for positive; **0** for 0 values; **-1** for "+
			"negative."),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Determines the sign of `val`: **1** for positive; **0** for 0 values; **-1** " +
				"for negative.",
		},
	),

	"sqrt": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			// TODO(mjibson): see #13642
			if x < 0 {
				return nil, errSqrtOfNegNumber
			}
			return tree.NewDFloat(tree.DFloat(math.Sqrt(x))), nil
		}, "Calculates the square root of `val`."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			if x.Sign() < 0 {
				return nil, errSqrtOfNegNumber
			}
			dd := &tree.DDecimal{}
			_, err := tree.DecimalCtx.Sqrt(&dd.Decimal, x)
			return dd, err
		}, "Calculates the square root of `val`."),
	),

	"tan": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Tan(x))), nil
		}, "Calculates the tangent of `val`."),
	),

	"trunc": makeBuiltin(defProps(),
		floatOverload1(func(x float64) (tree.Datum, error) {
			return tree.NewDFloat(tree.DFloat(math.Trunc(x))), nil
		}, "Truncates the decimal values of `val`."),
		decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
			dd := &tree.DDecimal{}
			x.Modf(&dd.Decimal, nil)
			return dd, nil
		}, "Truncates the decimal values of `val`."),
	),

	// Array functions.

	"string_to_array": makeBuiltin(arrayPropsNullableArgs(),
		tree.Overload{
			Types:      tree.ArgTypes{{"str", types.String}, {"delimiter", types.String}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: types.String}),
			Info:       "Split a string into components on a delimiter.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"str", types.String}, {"delimiter", types.String}, {"null", types.String}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: types.String}),
			Info:       "Split a string into components on a delimiter with a specified string to consider NULL.",
		},
	),

	"array_to_string": makeBuiltin(arrayPropsNullableArgs(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.AnyArray}, {"delim", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Join an array into a string with a delimiter.",
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.AnyArray}, {"delimiter", types.String}, {"null", types.String}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Join an array into a string with a delimiter, replacing NULLs with a null string.",
		},
	),

	"array_length": makeBuiltin(arrayProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.AnyArray}, {"array_dimension", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Calculates the length of `input` on the provided `array_dimension`. However, " +
				"because CockroachDB doesn't yet support multi-dimensional arrays, the only supported" +
				" `array_dimension` is **1**.",
		},
	),

	"array_lower": makeBuiltin(arrayProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.AnyArray}, {"array_dimension", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Calculates the minimum value of `input` on the provided `array_dimension`. " +
				"However, because CockroachDB doesn't yet support multi-dimensional arrays, the only " +
				"supported `array_dimension` is **1**.",
		},
	),

	"array_upper": makeBuiltin(arrayProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"input", types.AnyArray}, {"array_dimension", types.Int}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info: "Calculates the maximum value of `input` on the provided `array_dimension`. " +
				"However, because CockroachDB doesn't yet support multi-dimensional arrays, the only " +
				"supported `array_dimension` is **1**.",
		},
	),

	"array_append": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"array", types.TArray{Typ: typ}}, {"elem", typ}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: typ}),
			Info:       "Appends `elem` to `array`, returning the result.",
		}
	})),

	"array_prepend": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"elem", typ}, {"array", types.TArray{Typ: typ}}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: typ}),
			Info:       "Prepends `elem` to `array`, returning the result.",
		}
	})),

	"array_cat": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"left", types.TArray{Typ: typ}}, {"right", types.TArray{Typ: typ}}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: typ}),
			Info:       "Appends two arrays.",
		}
	})),

	"array_remove": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"array", types.TArray{Typ: typ}}, {"elem", typ}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: typ}),
			Info:       "Remove from `array` all elements equal to `elem`.",
		}
	})),

	"array_replace": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"array", types.TArray{Typ: typ}}, {"toreplace", typ}, {"replacewith", typ}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: typ}),
			Info:       "Replace all occurrences of `toreplace` in `array` with `replacewith`.",
		}
	})),

	"array_position": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"array", types.TArray{Typ: typ}}, {"elem", typ}},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       "Return the index of the first occurrence of `elem` in `array`.",
		}
	})),

	"array_positions": setProps(arrayPropsNullableArgs(), arrayBuiltin(func(typ types.T) tree.Overload {
		return tree.Overload{
			Types:      tree.ArgTypes{{"array", types.TArray{Typ: typ}}, {"elem", typ}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: types.Int}),
			Info:       "Returns and array of indexes of all occurrences of `elem` in `array`.",
		}
	})),

	// JSON functions.

	"json_remove_path": makeBuiltin(jsonProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.JSON}, {"path", types.TArray{Typ: types.String}}},
			ReturnType: tree.FixedReturnType(types.JSON),
			Info:       "Remove the specified path from the JSON object.",
		},
	),

	"json_extract_path": makeBuiltin(jsonProps(), jsonExtractPathImpl),

	"jsonb_extract_path": makeBuiltin(jsonProps(), jsonExtractPathImpl),

	"json_set": makeBuiltin(jsonProps(), jsonSetImpl, jsonSetWithCreateMissingImpl),

	"jsonb_set": makeBuiltin(jsonProps(), jsonSetImpl, jsonSetWithCreateMissingImpl),

	"jsonb_insert": makeBuiltin(jsonProps(), jsonInsertImpl, jsonInsertWithInsertAfterImpl),

	"jsonb_pretty": makeBuiltin(jsonProps(),
		tree.Overload{
			Types:      tree.ArgTypes{{"val", types.JSON}},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the given JSON value as a STRING indented and with newlines.",
		},
	),

	"json_typeof": makeBuiltin(jsonProps(), jsonTypeOfImpl),

	"jsonb_typeof": makeBuiltin(jsonProps(), jsonTypeOfImpl),

	"array_to_json": arrayToJSONImpls,

	"to_json": makeBuiltin(jsonProps(), toJSONImpl),

	"to_jsonb": makeBuiltin(jsonProps(), toJSONImpl),

	"json_build_array": makeBuiltin(jsonPropsNullableArgs(), jsonBuildArrayImpl),

	"jsonb_build_array": makeBuiltin(jsonPropsNullableArgs(), jsonBuildArrayImpl),

	"json_build_object": makeBuiltin(jsonPropsNullableArgs(), jsonBuildObjectImpl),

	"jsonb_build_object": makeBuiltin(jsonPropsNullableArgs(), jsonBuildObjectImpl),

	"json_object": jsonObjectImpls,

	"jsonb_object": jsonObjectImpls,

	"json_strip_nulls": makeBuiltin(jsonProps(), jsonStripNullsImpl),

	"jsonb_strip_nulls": makeBuiltin(jsonProps(), jsonStripNullsImpl),

	"json_array_length": makeBuiltin(jsonProps(), jsonArrayLengthImpl),

	"jsonb_array_length": makeBuiltin(jsonProps(), jsonArrayLengthImpl),

	// Metadata functions.

	// https://www.postgresql.org/docs/10/static/functions-info.html
	"version": makeBuiltin(
		tree.FunctionProperties{Category: categorySystemInfo},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the node's version of CockroachDB.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-info.html
	"current_database": makeBuiltin(
		tree.FunctionProperties{Category: categorySystemInfo},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the current database.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-info.html
	//
	// Note that in addition to what the pg doc says ("current_schema =
	// first item in search path"), the pg server actually skips over
	// non-existent schemas in the search path to determine
	// current_schema. This is not documented but can be verified by a
	// SQL client against a pg server.
	"current_schema": makeBuiltin(
		tree.FunctionProperties{
			Category:         categorySystemInfo,
			DistsqlBlacklist: true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       "Returns the current schema.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-info.html
	//
	// Note that in addition to what the pg doc says ("current_schemas =
	// items in search path with or without pg_catalog depending on
	// argument"), the pg server actually skips over non-existent
	// schemas in the search path to compute current_schemas. This is
	// not documented but can be verified by a SQL client against a pg
	// server.
	"current_schemas": makeBuiltin(
		tree.FunctionProperties{
			Category:         categorySystemInfo,
			DistsqlBlacklist: true,
		},
		tree.Overload{
			Types:      tree.ArgTypes{{"include_pg_catalog", types.Bool}},
			ReturnType: tree.FixedReturnType(types.TArray{Typ: types.String}),
			Info:       "Returns the valid schemas in the search path.",
		},
	),

	// https://www.postgresql.org/docs/10/static/functions-info.html
	"current_user": makeBuiltin(
		tree.FunctionProperties{Category: categorySystemInfo},
		tree.Overload{
			Types:      tree.ArgTypes{},
			ReturnType: tree.FixedReturnType(types.String),
			Info: "Returns the current user. This function is provided for " +
				"compatibility with PostgreSQL.",
		},
	),
}

var lengthImpls = makeBuiltin(tree.FunctionProperties{Category: categoryString},
	stringOverload1(types.Int, "Calculates the number of characters in `val`."),
	bytesOverload1(types.Int, "Calculates the number of bytes in `val`."),
)

var substringImpls = makeBuiltin(tree.FunctionProperties{Category: categoryString},
	tree.Overload{
		Types: tree.ArgTypes{
			{"input", types.String},
			{"substr_pos", types.Int},
		},
		ReturnType: tree.FixedReturnType(types.String),
		Info:       "Returns a substring of `input` starting at `substr_pos` (count starts at 1).",
	},
	tree.Overload{
		Types: tree.ArgTypes{
			{"input", types.String},
			{"start_pos", types.Int},
			{"end_pos", types.Int},
		},
		ReturnType: tree.FixedReturnType(types.String),
		Info:       "Returns a substring of `input` between `start_pos` and `end_pos` (count starts at 1).",
	},
	tree.Overload{
		Types: tree.ArgTypes{
			{"input", types.String},
			{"regex", types.String},
		},
		ReturnType: tree.FixedReturnType(types.String),
		Info:       "Returns a substring of `input` that matches the regular expression `regex`.",
	},
	tree.Overload{
		Types: tree.ArgTypes{
			{"input", types.String},
			{"regex", types.String},
			{"escape_char", types.String},
		},
		ReturnType: tree.FixedReturnType(types.String),
		Info: "Returns a substring of `input` that matches the regular expression `regex` using " +
			"`escape_char` as your escape character instead of `\\`.",
	},
)

var uuidV4Impl = makeBuiltin(
	tree.FunctionProperties{
		Category: categoryIDGeneration,
		Impure:   true,
	},
	tree.Overload{
		Types:      tree.ArgTypes{},
		ReturnType: tree.FixedReturnType(types.Bytes),
		Info:       "Returns a UUID.",
	},
)

var ceilImpl = makeBuiltin(defProps(),
	floatOverload1(func(x float64) (tree.Datum, error) {
		return tree.NewDFloat(tree.DFloat(math.Ceil(x))), nil
	}, "Calculates the smallest integer greater than `val`."),
	decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
		dd := &tree.DDecimal{}
		_, err := tree.ExactCtx.Ceil(&dd.Decimal, x)
		if dd.IsZero() {
			dd.Negative = false
		}
		return dd, err
	}, "Calculates the smallest integer greater than `val`."),
)

var txnTSContextDoc = `

The value is based on a timestamp picked when the transaction starts
and which stays constant throughout the transaction. This timestamp
has no relationship with the commit order of concurrent transactions.`

var txnTSDoc = `Returns the time of the current transaction.` + txnTSContextDoc

var txnTSImpl = makeBuiltin(
	tree.FunctionProperties{
		Category: categoryDateAndTime,
		Impure:   true,
	},
	tree.Overload{
		Types:             tree.ArgTypes{},
		ReturnType:        tree.FixedReturnType(types.TimestampTZ),
		PreferredOverload: true,
		Info:              txnTSDoc,
	},
	tree.Overload{
		Types:      tree.ArgTypes{},
		ReturnType: tree.FixedReturnType(types.Timestamp),
		Info:       txnTSDoc,
	},
)

var powImpls = makeBuiltin(defProps(),
	floatOverload2("x", "y", func(x, y float64) (tree.Datum, error) {
		return tree.NewDFloat(tree.DFloat(math.Pow(x, y))), nil
	}, "Calculates `x`^`y`."),
	decimalOverload2("x", "y", func(x, y *apd.Decimal) (tree.Datum, error) {
		dd := &tree.DDecimal{}
		_, err := tree.DecimalCtx.Pow(&dd.Decimal, x, y)
		return dd, err
	}, "Calculates `x`^`y`."),
	tree.Overload{
		Types: tree.ArgTypes{
			{"x", types.Int},
			{"y", types.Int},
		},
		ReturnType: tree.FixedReturnType(types.Int),
		Info:       "Calculates `x`^`y`.",
	},
)

var (
	jsonNullDString    = tree.NewDString("null")
	jsonStringDString  = tree.NewDString("string")
	jsonNumberDString  = tree.NewDString("number")
	jsonBooleanDString = tree.NewDString("boolean")
	jsonArrayDString   = tree.NewDString("array")
	jsonObjectDString  = tree.NewDString("object")
)

var (
	errJSONObjectNotEvenNumberOfElements = pgerror.NewError(pgerror.CodeInvalidParameterValueError,
		"array must have even number of elements")
	errJSONObjectNullValueForKey = pgerror.NewError(pgerror.CodeInvalidParameterValueError,
		"null value not allowed for object key")
	errJSONObjectMismatchedArrayDim = pgerror.NewError(pgerror.CodeInvalidParameterValueError,
		"mismatched array dimensions")
)

var jsonExtractPathImpl = tree.Overload{
	Types:      tree.VariadicType{FixedTypes: []types.T{types.JSON}, VarType: types.String},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Returns the JSON value pointed to by the variadic arguments.",
}

// darrayToStringSlice converts an array of string datums to a Go array of
// strings. If any of the elements are NULL, then ok will be returned as false.
func darrayToStringSlice(d tree.DArray) (result []string, ok bool) {
	result = make([]string, len(d.Array))
	for i, s := range d.Array {
		if s == tree.DNull {
			return nil, false
		}
		result[i] = string(tree.MustBeDString(s))
	}
	return result, true
}

// checkHasNulls returns an appropriate error if the array contains a NULL.
func checkHasNulls(ary tree.DArray) error {
	if ary.HasNulls {
		for i := range ary.Array {
			if ary.Array[i] == tree.DNull {
				return pgerror.NewErrorf(pgerror.CodeNullValueNotAllowedError, "path element at position %d is null", i+1)
			}
		}
	}
	return nil
}

var jsonSetImpl = tree.Overload{
	Types: tree.ArgTypes{
		{"val", types.JSON},
		{"path", types.TArray{Typ: types.String}},
		{"to", types.JSON},
	},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Returns the JSON value pointed to by the variadic arguments.",
}

var jsonSetWithCreateMissingImpl = tree.Overload{
	Types: tree.ArgTypes{
		{"val", types.JSON},
		{"path", types.TArray{Typ: types.String}},
		{"to", types.JSON},
		{"create_missing", types.Bool},
	},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info: "Returns the JSON value pointed to by the variadic arguments. " +
		"If `create_missing` is false, new keys will not be inserted to objects " +
		"and values will not be prepended or appended to arrays.",
}

func jsonDatumSet(
	targetD tree.Datum, pathD tree.Datum, toD tree.Datum, createMissingD tree.Datum,
) (tree.Datum, error) {
	ary := *tree.MustBeDArray(pathD)
	// jsonb_set only errors if there is a null at the first position, but not
	// at any other positions.
	if err := checkHasNulls(ary); err != nil {
		return nil, err
	}
	path, ok := darrayToStringSlice(ary)
	if !ok {
		return targetD, nil
	}
	j, err := json.DeepSet(tree.MustBeDJSON(targetD).JSON, path, tree.MustBeDJSON(toD).JSON, bool(tree.MustBeDBool(createMissingD)))
	if err != nil {
		return nil, err
	}
	return &tree.DJSON{JSON: j}, nil
}

var jsonInsertImpl = tree.Overload{
	Types: tree.ArgTypes{
		{"target", types.JSON},
		{"path", types.TArray{Typ: types.String}},
		{"new_val", types.JSON},
	},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Returns the JSON value pointed to by the variadic arguments. `new_val` will be inserted before path target.",
}

var jsonInsertWithInsertAfterImpl = tree.Overload{
	Types: tree.ArgTypes{
		{"target", types.JSON},
		{"path", types.TArray{Typ: types.String}},
		{"new_val", types.JSON},
		{"insert_after", types.Bool},
	},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info: "Returns the JSON value pointed to by the variadic arguments. " +
		"If `insert_after` is true (default is false), `new_val` will be inserted after path target.",
}

func insertToJSONDatum(
	targetD tree.Datum, pathD tree.Datum, newValD tree.Datum, insertAfterD tree.Datum,
) (tree.Datum, error) {
	ary := *tree.MustBeDArray(pathD)

	// jsonb_insert only errors if there is a null at the first position, but not
	// at any other positions.
	if err := checkHasNulls(ary); err != nil {
		return nil, err
	}
	path, ok := darrayToStringSlice(ary)
	if !ok {
		return targetD, nil
	}
	j, err := json.DeepInsert(tree.MustBeDJSON(targetD).JSON, path, tree.MustBeDJSON(newValD).JSON, bool(tree.MustBeDBool(insertAfterD)))
	if err != nil {
		return nil, err
	}
	return &tree.DJSON{JSON: j}, nil
}

var jsonTypeOfImpl = tree.Overload{
	Types:      tree.ArgTypes{{"val", types.JSON}},
	ReturnType: tree.FixedReturnType(types.String),
	Info:       "Returns the type of the outermost JSON value as a text string.",
}

func jsonProps() tree.FunctionProperties {
	return tree.FunctionProperties{
		Category: categoryJSON,
	}
}

func jsonPropsNullableArgs() tree.FunctionProperties {
	d := jsonProps()
	d.NullableArgs = true
	return d
}

var jsonBuildObjectImpl = tree.Overload{
	Types:      tree.VariadicType{VarType: types.Any},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Builds a JSON object out of a variadic argument list.",
}

var toJSONImpl = tree.Overload{
	Types:      tree.ArgTypes{{"val", types.Any}},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Returns the value as JSON or JSONB.",
}

var prettyPrintNotSupportedError = pgerror.NewErrorf(pgerror.CodeFeatureNotSupportedError, "pretty printing is not supported")

var arrayToJSONImpls = makeBuiltin(jsonProps(),
	tree.Overload{
		Types:      tree.ArgTypes{{"array", types.AnyArray}},
		ReturnType: tree.FixedReturnType(types.JSON),
		Info:       "Returns the array as JSON or JSONB.",
	},
	tree.Overload{
		Types:      tree.ArgTypes{{"array", types.AnyArray}, {"pretty_bool", types.Bool}},
		ReturnType: tree.FixedReturnType(types.JSON),
		Info:       "Returns the array as JSON or JSONB.",
	},
)

var jsonBuildArrayImpl = tree.Overload{
	Types:      tree.VariadicType{VarType: types.Any},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Builds a possibly-heterogeneously-typed JSON or JSONB array out of a variadic argument list.",
}

var jsonObjectImpls = makeBuiltin(jsonProps(),
	tree.Overload{
		Types:      tree.ArgTypes{{"texts", types.TArray{Typ: types.String}}},
		ReturnType: tree.FixedReturnType(types.JSON),
		Info: "Builds a JSON or JSONB object out of a text array. The array must have " +
			"exactly one dimension with an even number of members, in which case " +
			"they are taken as alternating key/value pairs.",
	},
	tree.Overload{
		Types: tree.ArgTypes{{"keys", types.TArray{Typ: types.String}},
			{"values", types.TArray{Typ: types.String}}},
		ReturnType: tree.FixedReturnType(types.JSON),
		Info: "This form of json_object takes keys and values pairwise from two " +
			"separate arrays. In all other respects it is identical to the " +
			"one-argument form.",
	},
)

var jsonStripNullsImpl = tree.Overload{
	Types:      tree.ArgTypes{{"from_json", types.JSON}},
	ReturnType: tree.FixedReturnType(types.JSON),
	Info:       "Returns from_json with all object fields that have null values omitted. Other null values are untouched.",
}

var jsonArrayLengthImpl = tree.Overload{
	Types:      tree.ArgTypes{{"json", types.JSON}},
	ReturnType: tree.FixedReturnType(types.Int),
	Info:       "Returns the number of elements in the outermost JSON or JSONB array.",
}

func arrayBuiltin(impl func(types.T) tree.Overload) builtinDefinition {
	overloads := make([]tree.Overload, 0, len(types.AnyNonArray))
	for _, typ := range types.AnyNonArray {
		if types.IsValidArrayElementType(typ) {
			overloads = append(overloads, impl(typ))
		}
	}
	return builtinDefinition{
		props:     tree.FunctionProperties{Category: categoryArray},
		overloads: overloads,
	}
}

func setProps(props tree.FunctionProperties, d builtinDefinition) builtinDefinition {
	d.props = props
	return d
}

func decimalLogFn(
	logFn func(*apd.Decimal, *apd.Decimal) (apd.Condition, error), info string,
) tree.Overload {
	return decimalOverload1(func(x *apd.Decimal) (tree.Datum, error) {
		// TODO(mjibson): see #13642
		switch x.Sign() {
		case -1:
			return nil, errLogOfNegNumber
		case 0:
			return nil, errLogOfZero
		}
		dd := &tree.DDecimal{}
		_, err := logFn(&dd.Decimal, x)
		return dd, err
	}, info)
}

func floatOverload1(f func(float64) (tree.Datum, error), info string) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{"val", types.Float}},
		ReturnType: tree.FixedReturnType(types.Float),
		Info:       info,
	}
}

func floatOverload2(
	a, b string, f func(float64, float64) (tree.Datum, error), info string,
) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{a, types.Float}, {b, types.Float}},
		ReturnType: tree.FixedReturnType(types.Float),
		Info:       info,
	}
}

func decimalOverload1(f func(*apd.Decimal) (tree.Datum, error), info string) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{"val", types.Decimal}},
		ReturnType: tree.FixedReturnType(types.Decimal),
		Info:       info,
	}
}

func decimalOverload2(
	a, b string, f func(*apd.Decimal, *apd.Decimal) (tree.Datum, error), info string,
) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{a, types.Decimal}, {b, types.Decimal}},
		ReturnType: tree.FixedReturnType(types.Decimal),
		Info:       info,
	}
}

func stringOverload1(
	returnType types.T, info string,
) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{"val", types.String}},
		ReturnType: tree.FixedReturnType(returnType),
		Info:       info,
	}
}

func stringOverload2(
	a, b string,
	returnType types.T,
	info string,
) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{a, types.String}, {b, types.String}},
		ReturnType: tree.FixedReturnType(returnType),
		Info:       info,
	}
}

func stringOverload3(
	a, b, c string,
	returnType types.T,
	info string,
) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{a, types.String}, {b, types.String}, {c, types.String}},
		ReturnType: tree.FixedReturnType(returnType),
		Info:       info,
	}
}

func bytesOverload1(
	returnType types.T, info string,
) tree.Overload {
	return tree.Overload{
		Types:      tree.ArgTypes{{"val", types.Bytes}},
		ReturnType: tree.FixedReturnType(returnType),
		Info:       info,
	}
}

// feedHash returns true if it encounters any non-Null datum.
func feedHash(h hash.Hash, args tree.Datums) bool {
	var nonNullSeen bool
	for _, datum := range args {
		if datum == tree.DNull {
			continue
		} else {
			nonNullSeen = true
		}
		var buf string
		if d, ok := datum.(*tree.DBytes); ok {
			buf = string(*d)
		} else {
			buf = string(tree.MustBeDString(datum))
		}
		_, err := h.Write([]byte(buf))
		if err != nil {
			panic(errors.Wrap(err, `"It never returns an error." -- https://golang.org/pkg/hash`))
		}
	}
	return nonNullSeen
}

func hashBuiltin(newHash func() hash.Hash, info string) builtinDefinition {
	return makeBuiltin(tree.FunctionProperties{NullableArgs: true},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.String},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       info,
		},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.Bytes},
			ReturnType: tree.FixedReturnType(types.String),
			Info:       info,
		},
	)
}

func hash32Builtin(newHash func() hash.Hash32, info string) builtinDefinition {
	return makeBuiltin(tree.FunctionProperties{NullableArgs: true},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.String},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       info,
		},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.Bytes},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       info,
		},
	)
}

func hash64Builtin(newHash func() hash.Hash64, info string) builtinDefinition {
	return makeBuiltin(tree.FunctionProperties{NullableArgs: true},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.String},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       info,
		},
		tree.Overload{
			Types:      tree.VariadicType{VarType: types.Bytes},
			ReturnType: tree.FixedReturnType(types.Int),
			Info:       info,
		},
	)
}

type regexpEscapeKey struct {
	sqlPattern string
	sqlEscape  string
}

// Pattern implements the RegexpCacheKey interface.
func (k regexpEscapeKey) Pattern() (string, error) {
	pattern := k.sqlPattern
	if k.sqlEscape != `\` {
		pattern = strings.Replace(pattern, `\`, `\\`, -1)
		pattern = strings.Replace(pattern, k.sqlEscape, `\`, -1)
	}
	return pattern, nil
}

type regexpFlagKey struct {
	sqlPattern string
	sqlFlags   string
}

// Pattern implements the RegexpCacheKey interface.
func (k regexpFlagKey) Pattern() (string, error) {
	return regexpEvalFlags(k.sqlPattern, k.sqlFlags)
}

var flagToByte = map[syntax.Flags]byte{
	syntax.FoldCase: 'i',
	syntax.DotNL:    's',
}

var flagToNotByte = map[syntax.Flags]byte{
	syntax.OneLine: 'm',
}

// regexpEvalFlags evaluates the provided Postgres regexp flags in
// accordance with their definitions provided at
// http://www.postgresql.org/docs/9.0/static/functions-matching.html#POSIX-EMBEDDED-OPTIONS-TABLE.
// It then returns an adjusted regexp pattern.
func regexpEvalFlags(pattern, sqlFlags string) (string, error) {
	flags := syntax.DotNL | syntax.OneLine

	for _, sqlFlag := range sqlFlags {
		switch sqlFlag {
		case 'g':
			// Handled in `regexpReplace`.
		case 'i':
			flags |= syntax.FoldCase
		case 'c':
			flags &^= syntax.FoldCase
		case 's':
			flags &^= syntax.DotNL
		case 'm', 'n':
			flags &^= syntax.DotNL
			flags &^= syntax.OneLine
		case 'p':
			flags &^= syntax.DotNL
			flags |= syntax.OneLine
		case 'w':
			flags |= syntax.DotNL
			flags &^= syntax.OneLine
		default:
			return "", pgerror.NewErrorf(
				pgerror.CodeInvalidRegularExpressionError, "invalid regexp flag: %q", sqlFlag)
		}
	}

	var goFlags bytes.Buffer
	for flag, b := range flagToByte {
		if flags&flag != 0 {
			goFlags.WriteByte(b)
		}
	}
	for flag, b := range flagToNotByte {
		if flags&flag == 0 {
			goFlags.WriteByte(b)
		}
	}
	// Bytes() instead of String() to save an allocation.
	bs := goFlags.Bytes()
	if len(bs) == 0 {
		return pattern, nil
	}
	return fmt.Sprintf("(?%s:%s)", bs, pattern), nil
}

func overlay(s, to string, pos, size int) (tree.Datum, error) {
	if pos < 1 {
		return nil, pgerror.NewErrorf(
			pgerror.CodeInvalidParameterValueError, "non-positive substring length not allowed: %d", pos)
	}
	pos--

	runes := []rune(s)
	if pos > len(runes) {
		pos = len(runes)
	}
	after := pos + size
	if after < 0 {
		after = 0
	} else if after > len(runes) {
		after = len(runes)
	}
	return tree.NewDString(string(runes[:pos]) + to + string(runes[after:])), nil
}

func roundDecimal(x *apd.Decimal, n int32) (tree.Datum, error) {
	dd := &tree.DDecimal{}
	_, err := tree.HighPrecisionCtx.Quantize(&dd.Decimal, x, -n)
	return dd, err
}

var uniqueIntState struct {
	syncutil.Mutex
	timestamp uint64
}

var uniqueIntEpoch = time.Date(2015, time.January, 1, 0, 0, 0, 0, time.UTC).UnixNano()

// NodeIDBits is the number of bits stored in the lower portion of
// GenerateUniqueInt.
const NodeIDBits = 15

// GenerateUniqueID encapsulates the logic to generate a unique number from
// a nodeID and timestamp.
func GenerateUniqueID(nodeID int32, timestamp uint64) tree.DInt {
	// We xor in the nodeID so that nodeIDs larger than 32K will flip bits in the
	// timestamp portion of the final value instead of always setting them.
	id := (timestamp << NodeIDBits) ^ uint64(nodeID)
	return tree.DInt(id)
}

func arrayLength(arr *tree.DArray, dim int64) tree.Datum {
	if arr.Len() == 0 || dim < 1 {
		return tree.DNull
	}
	if dim == 1 {
		return tree.NewDInt(tree.DInt(arr.Len()))
	}
	a, ok := tree.AsDArray(arr.Array[0])
	if !ok {
		return tree.DNull
	}
	return arrayLength(a, dim-1)
}

var intOne = tree.NewDInt(tree.DInt(1))

func arrayLower(arr *tree.DArray, dim int64) tree.Datum {
	if arr.Len() == 0 || dim < 1 {
		return tree.DNull
	}
	if dim == 1 {
		return intOne
	}
	a, ok := tree.AsDArray(arr.Array[0])
	if !ok {
		return tree.DNull
	}
	return arrayLower(a, dim-1)
}

const microsPerMilli = 1000

func extractStringFromTime(fromTime *tree.DTime, timeSpan string) (tree.Datum, error) {
	t := timeofday.TimeOfDay(*fromTime)
	switch timeSpan {
	case "hour", "hours":
		return tree.NewDInt(tree.DInt(t.Hour())), nil
	case "minute", "minutes":
		return tree.NewDInt(tree.DInt(t.Minute())), nil
	case "second", "seconds":
		return tree.NewDInt(tree.DInt(t.Second())), nil
	case "millisecond", "milliseconds":
		return tree.NewDInt(tree.DInt(t.Microsecond() / microsPerMilli)), nil
	case "microsecond", "microseconds":
		return tree.NewDInt(tree.DInt(t.Microsecond())), nil
	case "epoch":
		seconds := time.Duration(t) * time.Microsecond / time.Second
		return tree.NewDInt(tree.DInt(int64(seconds))), nil
	default:
		return nil, pgerror.NewErrorf(
			pgerror.CodeInvalidParameterValueError, "unsupported timespan: %s", timeSpan)
	}
}

func extractStringFromTimestamp(
	fromTime time.Time, timeSpan string,
) (tree.Datum, error) {
	switch timeSpan {
	case "year", "years":
		return tree.NewDInt(tree.DInt(fromTime.Year())), nil

	case "quarter":
		return tree.NewDInt(tree.DInt((fromTime.Month()-1)/3 + 1)), nil

	case "month", "months":
		return tree.NewDInt(tree.DInt(fromTime.Month())), nil

	case "week", "weeks":
		_, week := fromTime.ISOWeek()
		return tree.NewDInt(tree.DInt(week)), nil

	case "day", "days":
		return tree.NewDInt(tree.DInt(fromTime.Day())), nil

	case "dayofweek", "dow":
		return tree.NewDInt(tree.DInt(fromTime.Weekday())), nil

	case "dayofyear", "doy":
		return tree.NewDInt(tree.DInt(fromTime.YearDay())), nil

	case "hour", "hours":
		return tree.NewDInt(tree.DInt(fromTime.Hour())), nil

	case "minute", "minutes":
		return tree.NewDInt(tree.DInt(fromTime.Minute())), nil

	case "second", "seconds":
		return tree.NewDInt(tree.DInt(fromTime.Second())), nil

	case "millisecond", "milliseconds":
		// This a PG extension not supported in MySQL.
		return tree.NewDInt(tree.DInt(fromTime.Nanosecond() / int(time.Millisecond))), nil

	case "microsecond", "microseconds":
		return tree.NewDInt(tree.DInt(fromTime.Nanosecond() / int(time.Microsecond))), nil

	case "epoch":
		return tree.NewDInt(tree.DInt(fromTime.Unix())), nil

	default:
		return nil, pgerror.NewErrorf(pgerror.CodeInvalidParameterValueError, "unsupported timespan: %s", timeSpan)
	}
}

func truncateTime(fromTime *tree.DTime, timeSpan string) (*tree.DTime, error) {
	t := timeofday.TimeOfDay(*fromTime)
	hour := t.Hour()
	min := t.Minute()
	sec := t.Second()
	micro := t.Microsecond()

	minTrunc := 0
	secTrunc := 0
	microTrunc := 0

	switch timeSpan {
	case "hour", "hours":
		min, sec, micro = minTrunc, secTrunc, microTrunc
	case "minute", "minutes":
		sec, micro = secTrunc, microTrunc
	case "second", "seconds":
		micro = microTrunc
	case "millisecond", "milliseconds":
		// This a PG extension not supported in MySQL.
		micro = (micro / microsPerMilli) * microsPerMilli
	case "microsecond", "microseconds":
	default:
		return nil, pgerror.NewErrorf(pgerror.CodeInvalidParameterValueError, "unsupported timespan: %s", timeSpan)
	}

	return tree.MakeDTime(timeofday.New(hour, min, sec, micro)), nil
}

func stringOrNil(d tree.Datum) *string {
	if d == tree.DNull {
		return nil
	}
	s := string(tree.MustBeDString(d))
	return &s
}

// stringToArray implements the string_to_array builtin - str is split on delim to form an array of strings.
// If nullStr is set, any elements equal to it will be NULL.
func stringToArray(str string, delimPtr *string, nullStr *string) (tree.Datum, error) {
	var split []string

	if delimPtr != nil {
		delim := *delimPtr
		if str == "" {
			split = nil
		} else if delim == "" {
			split = []string{str}
		} else {
			split = strings.Split(str, delim)
		}
	} else {
		// When given a NULL delimiter, string_to_array splits into each character.
		split = make([]string, len(str))
		for i, c := range str {
			split[i] = string(c)
		}
	}

	result := tree.NewDArray(types.String)
	for _, s := range split {
		var next tree.Datum = tree.NewDString(s)
		if nullStr != nil && s == *nullStr {
			next = tree.DNull
		}
		if err := result.Append(next); err != nil {
			return nil, err
		}
	}
	return result, nil
}

// arrayToString implements the array_to_string builtin - arr is joined using
// delim. If nullStr is non-nil, NULL values in the array will be replaced by
// it.
func arrayToString(arr *tree.DArray, delim string, nullStr *string) (tree.Datum, error) {
	f := tree.NewFmtCtxWithBuf(tree.FmtParseDatums)

	for i := range arr.Array {
		if arr.Array[i] == tree.DNull {
			if nullStr == nil {
				continue
			}
			f.WriteString(*nullStr)
		} else {
			f.FormatNode(arr.Array[i])
		}
		if i < len(arr.Array)-1 {
			f.WriteString(delim)
		}
	}
	return tree.NewDString(f.CloseAndGetString()), nil
}

// encodeEscape implements the encode(..., 'escape') Postgres builtin. It's
// described "escape converts zero bytes and high-bit-set bytes to octal
// sequences (\nnn) and doubles backslashes."
func encodeEscape(input []byte) string {
	var result bytes.Buffer
	start := 0
	for i := range input {
		if input[i] == 0 || input[i]&128 != 0 {
			result.Write(input[start:i])
			start = i + 1
			result.WriteString(fmt.Sprintf(`\%03o`, input[i]))
		} else if input[i] == '\\' {
			result.Write(input[start:i])
			start = i + 1
			result.WriteString(`\\`)
		}
	}
	result.Write(input[start:])
	return result.String()
}

var errInvalidSyntaxForDecode = pgerror.NewError(pgerror.CodeInvalidParameterValueError, "invalid syntax for decode(..., 'escape')")

func isOctalDigit(c byte) bool {
	return '0' <= c && c <= '7'
}

func decodeOctalTriplet(input string) byte {
	return (input[0]-'0')*64 + (input[1]-'0')*8 + (input[2] - '0')
}

// decodeEscape implements the decode(..., 'escape') Postgres builtin. The
// escape format is described as "escape converts zero bytes and high-bit-set
// bytes to octal sequences (\nnn) and doubles backslashes."
func decodeEscape(input string) ([]byte, error) {
	result := make([]byte, 0, len(input))
	for i := 0; i < len(input); i++ {
		if input[i] == '\\' {
			if i+1 < len(input) && input[i+1] == '\\' {
				result = append(result, '\\')
				i++
			} else if i+3 < len(input) &&
				isOctalDigit(input[i+1]) &&
				isOctalDigit(input[i+2]) &&
				isOctalDigit(input[i+3]) {
				result = append(result, decodeOctalTriplet(input[i+1:i+4]))
				i += 3
			} else {
				return nil, errInvalidSyntaxForDecode
			}
		} else {
			result = append(result, input[i])
		}
	}
	return result, nil
}

func truncateTimestamp(
	fromTime time.Time, timeSpan string,
) (*tree.DTimestampTZ, error) {
	year := fromTime.Year()
	month := fromTime.Month()
	day := fromTime.Day()
	hour := fromTime.Hour()
	min := fromTime.Minute()
	sec := fromTime.Second()
	nsec := fromTime.Nanosecond()
	loc := fromTime.Location()

	monthTrunc := time.January
	dayTrunc := 1
	hourTrunc := 0
	minTrunc := 0
	secTrunc := 0
	nsecTrunc := 0

	switch timeSpan {
	case "year", "years":
		month, day, hour, min, sec, nsec = monthTrunc, dayTrunc, hourTrunc, minTrunc, secTrunc, nsecTrunc

	case "quarter":
		firstMonthInQuarter := ((month-1)/3)*3 + 1
		month, day, hour, min, sec, nsec = firstMonthInQuarter, dayTrunc, hourTrunc, minTrunc, secTrunc, nsecTrunc

	case "month", "months":
		day, hour, min, sec, nsec = dayTrunc, hourTrunc, minTrunc, secTrunc, nsecTrunc

	case "week", "weeks":
		// Subtract (day of week * nanoseconds per day) to get date as of previous Sunday.
		previousSunday := fromTime.Add(time.Duration(-1 * int64(fromTime.Weekday()) * int64(time.Hour) * 24))
		year, month, day = previousSunday.Year(), previousSunday.Month(), previousSunday.Day()
		hour, min, sec, nsec = hourTrunc, minTrunc, secTrunc, nsecTrunc

	case "day", "days":
		hour, min, sec, nsec = hourTrunc, minTrunc, secTrunc, nsecTrunc

	case "hour", "hours":
		min, sec, nsec = minTrunc, secTrunc, nsecTrunc

	case "minute", "minutes":
		sec, nsec = secTrunc, nsecTrunc

	case "second", "seconds":
		nsec = nsecTrunc

	case "millisecond", "milliseconds":
		// This a PG extension not supported in MySQL.
		milliseconds := (nsec / int(time.Millisecond)) * int(time.Millisecond)
		nsec = milliseconds

	case "microsecond", "microseconds":
		microseconds := (nsec / int(time.Microsecond)) * int(time.Microsecond)
		nsec = microseconds

	default:
		return nil, pgerror.NewErrorf(pgerror.CodeInvalidParameterValueError, "unsupported timespan: %s", timeSpan)
	}

	toTime := time.Date(year, month, day, hour, min, sec, nsec, loc)
	return tree.MakeDTimestampTZ(toTime, time.Microsecond), nil
}

// Converts a scalar Datum to its string representation
func asJSONBuildObjectKey(d tree.Datum) (string, error) {
	switch t := d.(type) {
	case *tree.DJSON, *tree.DArray, *tree.DTuple:
		return "", pgerror.NewError(pgerror.CodeInvalidParameterValueError,
			"key value must be scalar, not array, tuple, or json")
	case *tree.DString:
		return string(*t), nil
	case *tree.DCollatedString:
		return t.Contents, nil
	case *tree.DBool, *tree.DInt, *tree.DFloat, *tree.DDecimal, *tree.DTimestamp, *tree.DTimestampTZ, *tree.DDate, *tree.DUuid, *tree.DInterval, *tree.DBytes, *tree.DIPAddr, *tree.DOid, *tree.DTime:
		return tree.AsStringWithFlags(d, tree.FmtBareStrings), nil
	default:
		return "", pgerror.NewAssertionErrorf("unexpected type %T for key value", d)
	}
}

func asJSONObjectKey(d tree.Datum) (string, error) {
	switch t := d.(type) {
	case *tree.DString:
		return string(*t), nil
	default:
		return "", pgerror.NewAssertionErrorf("unexpected type %T for asJSONObjectKey", d)
	}
}

func toJSONObject(d tree.Datum) (tree.Datum, error) {
	j, err := tree.AsJSON(d)
	if err != nil {
		return nil, err
	}
	return tree.NewDJSON(j), nil
}

// padMaybeTruncate truncates the input string to length if the string is
// longer or equal in size to length. If truncated, the first return value
// will be true, and the last return value will be the truncated string.
// The second return value is set to the length of the input string in runes.
func padMaybeTruncate(s string, length int, fill string) (ok bool, slen int, ret string) {
	if length < 0 {
		// lpad and rpad both return an empty string if the input length is
		// negative.
		length = 0
	}
	slen = utf8.RuneCountInString(s)
	if length == slen {
		return true, slen, s
	}

	// If string is longer then length truncate it to the requested number
	// of characters.
	if length < slen {
		return true, slen, string([]rune(s)[:length])
	}

	// If the input fill is the empty string, return the original string.
	if len(fill) == 0 {
		return true, slen, s
	}

	return false, slen, s
}

// CleanEncodingName sanitizes the string meant to represent a
// recognized encoding. This ignores any non-alphanumeric character.
//
// See function clean_encoding_name() in postgres' sources
// in backend/utils/mb/encnames.c.
func CleanEncodingName(s string) string {
	b := make([]byte, 0, len(s))
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c >= 'A' && c <= 'Z' {
			b = append(b, c-'A'+'a')
		} else if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') {
			b = append(b, c)
		}
	}
	return string(b)
}
