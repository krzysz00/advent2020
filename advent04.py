#!/usr/bin/env python3
import fileinput
import re
import typing

def parse_records() -> list[dict[str, str]]:
    ret = []
    ret_single = {}
    for line in fileinput.input():
        if len(line.strip()) == 0:
            if len(ret_single) > 0:
                ret.append(ret_single)
            ret_single = {}
        else:
            for w in line.split():
                k, v = w.split(':')
                ret_single[k] = v
    if len(ret_single) > 0:
        ret.append(ret_single)
    return ret

def valid_a(record: dict[str, str]) -> bool:
    return record.keys() >= {"byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"}

def valid_b(record: dict[str, str]) -> bool:
    return (bool(re.match('^(19[2-9][0-9]|200[0-2])$', record.get("byr", "")))
            and bool(re.match('^20(20|1[0-9])$', record.get("iyr", "")))
            and bool(re.match('^20(30|2[0-9])$', record.get("eyr", "")))
            and bool(re.match('^(1[5-8][0-9]cm|19[0-3]cm|59in|6[0-9]in|7[0-6]in)$', record.get("hgt", "")))
            and bool(re.match('^#[0-9a-f]{6}$', record.get("hcl", "")))
            and bool(re.match('^(amb|blu|brn|gry|grn|hzl|oth)$', record.get("ecl", "")))
            and bool(re.match('^[0-9]{9}$', record.get("pid", ""))))

if __name__ == '__main__':
    records = parse_records()
    print(f"Part a: {sum((valid_a(r) for r in records))}")
    print(f"Part b: {sum((valid_b(r) for r in records))}")
