---
title: Half a decade of Property based testing at Equinor
author: Eivind Jahren
patat:
    eval:
        bash:
            command: bash
...


---

# In the beginning

---

# Agenda

* Get efficient with python hypothesis
* Compare property-based testing with other methods
* Experiences

---

# What is fuzzing

```bash
for file in `ls`
do
echo "$file"
done
```

---

# Fuzzing highlights:

* AFL (nginx, man, firefox)
* Shellshock
* google/oss-fuzz (sqlite3, ffmpeg, openssl)

---

# Only sad paths? Let's draw some happy examples...

---

# Perspective: Property based testing is just fuzzing for unit tests

---

# An example: Sorting is permuting


```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(elements=st.integers(min_value=5)))
def test_sorting_results_in_permutation(list):
    sorted_list = sorted(list)
    for element in list:
        assert element in sorted_list
    for element in sorted_list:
        assert element in list
```

---

# Example 2: Sorting orders


```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(elements=st.integers(min_value=5)))
def test_sorting_orders(list):
    sorted_list = sorted(list)
    for i in range(len(sorted_list)-1):
        assert sorted_list[i] <= sorted_list[i+1]
```
---

# Example 3: Read/Write roundtrip


```python
import yaml
from io import StringIO

@given(st.dictionaries(keys=st.text(), values=st.text()))
def test_reading_and_writing_yaml_are_inverses(data):
    buffer = StringIO()
    yaml.dump(data, buffer)
    buffer.seek(0)
    assert yaml.load(buffer) == data

```
---

# Reflection 1: Models of program verification

* Functions f and g are right-inverse if for all x:A . f(g(x)) = x
* Functions f and g are left-inverse if for all x:A . g(f(x)) = x
* f and g are inverse if they are both right-inverse and left-inverse.
* yaml.dump and yaml.load are inverse functions.

---

# Design by contract

```python
from icontract import ensure, require


@require(lambda list: elements_have_total_order(list))
@ensure(lambda result: is_ordered(result))
def sorted(list):
    ...
```

---

# Design by contract: Another example

```python
from icontract import ensure, require


@require(lambda a: a > 0)
@ensure(lambda result: (
    product(result) == a and
    all(is_prime(r) for r in result)
  )
)
def divisors(a:int) -> List[int]:
    ...
```

---

(btw, icontract can ghostwrite hypothesis tests)

...

wait what?

----

```python
@given(st.integers().filter(lambda a > 0))
def test_divisors_postcondition(a):
    result = divisors(a)
    assert product(result) == a and all(is_prime(r) for r in result)
```
----

```python
@given(st.integers(min_value=0))
def test_divisors_is_inverse_of_product(a):
    assert product(divisors(a)) == a

```

----

```python
@given(st.integers(min_value=0), st.integers(min_value=0))
def test_divisors_are_prime(a, i):
    result = divisors(a)
    assert is_prime(result[i % len(result)])
```
