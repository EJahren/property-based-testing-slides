---
title: Half a decade of PBT at Equinor
author: Eivind Jahren
patat:
    eval:
        bash:
            command: bash
...


---

# In the beginning

-------------------------------------------------

# Agenda

* Get efficient with python hypothesis
* Compare property-based testing with other methods
* Experiences

-------------------------------------------------

# What is Property-based testing (PBT) ?

-------------------------------------------------

# Perspective: PBT is just fuzzing for unit tests

-------------------------------------------------


# What is fuzzing

```bash
python3 generate_random_text.py
```

--------------------------------------------------

```bash
for ((i=1; i < 10; i++))
do
python3 generate_random_text.py > test.yml
python3 pretty_print_yaml.py test.yml pretty.yml
done
```
--------------------------------------------------

# Only sad paths? Let's draw some happy examples...

```bash
python3 generate_random_yaml.py
```
--------------------------------------------------

```bash
for ((i=1; i < 5; i++))
do
python3 generate_random_yaml.py > test.yml
python3 pretty_print_yaml.py test.yml pretty.yml
done
cat pretty.yml
```
--------------------------------------------------

```bash
for ((i=1; i < 5; i++))
do
python3 generate_random_yaml.py > test.yml
python3 pretty_print_yaml.py test.yml pretty.yml
python3 pretty_print_yaml.py pretty.yml pretty2.yml
diff pretty.yml pretty2.yml
done
```

---------------------------------------------------

# Fuzzing highlights:

* AFL (nginx, man, firefox)
* Shellshock
* google/oss-fuzz (sqlite3, ffmpeg, openssl)

---------------------------------------------------

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

---------------------------------------------------

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
----------------------------------------------------

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
-----------------------------------------------------------------

* Functions f and g are right-inverse if for all x:A . f(g(x)) = x
* Functions f and g are left-inverse if for all x:A . g(f(x)) = x
* f and g are inverse if they are both right-inverse and left-inverse.
* yaml.dump and yaml.load are inverse functions.

---------------------------------------------------------------

# Perspective: PBT is a gateway drug to Formal Methods

See for instance Frama-C:
```c
/*@ requires 0 <= n && \valid(a+(0..n-1));
    assigns \nothing;
    ensures \result == -1 ==> (\forall integer i; 0<= i < n ==> a[i] != v);
    ensures 0 <= \result < n ==> a[\result] == v;
    ensures -1 <= \result < n;
 */
int find(int n, const int a[], int v)
{
  int i;

  /*@ loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> a[j] != v;
      loop assigns i;
      loop variant n - i; */
  for (i=0; i < n; i++) {
    if (a[i] == v) {
      return i;
    }
  }

  return -1;
}
```

----------------------------------------------------------------

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

----

# Writing your own generators

----

# Do I really need hypothesis? Why not just rand and loop?

* Killer feature: shrinking
* Reproducing failures
* Tuning the number/size of examples
* CI logs
* Complicated data

----

# Shrinking

```python
def average(numbers):
    return sum(numbers) / len(numbers)


@given(st.lists(st.floats(), min_size=1))
def test_that_average_does_not_exceed_max(numbers):
    assert max(numbers) >= average(numbers)
```
