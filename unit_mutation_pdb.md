---
title: bugs, testing and specification
author: Eivind Jahren
patat:
    eval:
        python:
            command: python3
        bash:
            command: bash

    images:
        backend: auto
...


---

READY.
█

-------------------------------------------------

# Agenda

* Famous bugs
* Coverage and mutation testing
* Some background on PBD
* Using Hypothesis


-------------------------------------------------

# The therac-25

> Accidents usually involve a complex web of
> interacting events with multiple contributing
> factors.

- An Investigation of the Therac-25 Accidents (1993)

-------------------------------------------------

> The manufacturer said that the hardward
> and software were "tested and exercised separately or
> together for many years \[...\] A "small amount" of
> software testing was done on a simulator, but most
> testing was done as a system \[...\] quality
> assurance manager said that the Therac-25 software
> was tested for 2,700 hours.

- An Investigation of the Therac-25 Accidents (1993)

-------------------------------------------------

> System testing should be automated as well. A collection of executable
> programs should be produced and maintained to exercise all parts of the
> system. The set should be open ended and maintenance utilities should be
> included

- NATO SOFTWARE ENGINEERING CONFERENCE 1968

-------------------------------------------------

Simple Testing Can Prevent Most Critical Failures:
An Analysis of Production Failures in Distributed Data-Intensive Systems

usenix.org/system/files/conference/osdi14/osdi14-paper-yuan.pdf

-------------------------------------------------

> A majority of the production failures (77%) can be reproduced by a unit test.

usenix.org/system/files/conference/osdi14/osdi14-paper-yuan.pdf

-------------------------------------------------


# Power Peg (Knights Capital Group failure)

> In the week before go-live, a Knight engineer manually deployed the new RLP
> code in SMARS to its eight servers. However, the engineer made a mistake and
> did not copy the new code to one of the servers.

https://www.henricodolfing.com/2019/06/project-failure-case-study-knight-capital.html

-------------------------------------------------

# Power Peg (Knights Captal Group failure)

> The new RLP code in SMARS replaced some unused code in the relevant portion
> of the order router; the old code previously had been used for an order
> algorithm called “Power Peg,” which Knight had stopped using since 2003.
> Power Peg was a test program that bought high and sold low; it was
> specifically designed to move stock prices higher and lower in order to
> verify the behavior of its other proprietary trading algorithms in a
> controlled environment.

https://www.henricodolfing.com/2019/06/project-failure-case-study-knight-capital.html

-------------------------------------------------

# Driverless car crashes due to NaN

> "So during this initialization lap something happened which apparently caused
> the steering control signal to go to NaN and subsequently the steering locked
> to the maximum value to the right. When our car was given a permission to
> drive, the acceleration command went as normal \[...\]"

> "Ironically, [the NaN value] did show up on telemetry monitors, but it showed
> up along with 1.5k other telemetry values.

> while the team did code in many fail-safes in other areas of the application,
> it unfortunately only contained data validation on valid numbers

https://www.thedrive.com/news/37366/why-that-autonomous-race-car-crashed-straight-into-a-wall

-------------------------------------------------

```python

import numpy as np

def validate(a):
    if a < 0:
        raise ValueError()
    if a > 1:
        raise ValueError()

validate(np.nan)
```

-------------------------------------------------

```python

import numpy as np

def validate(a):
    if a < 0:
        raise ValueError()
    if a > 1:
        raise ValueError()

    assert a >= 0 and a <= 1

validate(np.nan)
```

-------------------------------------------------


> Test Early. Test Often. Test Automatically.

- "The pragmatic programmer" - Andrew Hunt & David Thomas



-------------------------------------------------

# The custodians of detail

```python

def gassman_equation(
        dry_bulk_modulus, mineral_bulk_modulus, fluid_bulk_modulus, porosity
    ):
    # Avseth et al.,"Quantitative Seismic Interpretation", page 17:
    difference_factor = dry_bulk_modulus / (
        mineral_bulk_modulus - dry_bulk_modulus
    ) + fluid_bulk_modulus / (
        (mineral_bulk_modulus - fluid_bulk_modulus) * porosity
    )

    if difference_factor < 0:
        raise ValueError("moduli of materials are unsuitable for fluid substitution")

    return difference_factor / (1 + difference_factor) * mineral_bulk_modulus

```


-------------------------------------------------


# Lets do something simpler

> To be a leap year, the year number must be divisible by four – except for
> years divisble by 100, unless they are also be divisible by 400.


For more, see Kevlin Henneys talk: https://youtu.be/-WWIeXmm4ec

-------------------------------------------------

# lets be specific

* A year is just a whole number
* There are leap years and non-leap years (sometimes called normal years)

* years not divisible by 4 are non-leap years
* years divisible by 4 and not by 100 are leap years
* years divisible 400 are leap years
* years divisible by 100 and not divisible by 400

-------------------------------------------------

> "When I use a word," Humpty Dumpty said in rather a scornful tone, "it means
> just what I choose it to mean — neither more nor less."
> "The question is," said Alice, "whether you can make words mean so many
> different things."

Lewis Carroll - Alice in Wonderland

-------------------------------------------------

```python
import pytest

@pytest.mark.parametrize("year", [1939, 1945, 1997, 1999])
def test_years_divisible_by_four_are_leap_years(year):
    assert not is_leap_year(year)
```

-------------------------------------------------

```python
def is_leap_year(year:int) -> bool:
    return False
```

-------------------------------------------------


```python
import pytest

@pytest.mark.parametrize("year", [1908, 1914, 1918, 1940, 1998, 2004])
def test_years_divisible_by_4_and_not_by_100_are_leap_years(year):
    assert is_leap_year(year)
```

-------------------------------------------------


```python
def is_leap_year(year: int) -> bool:
    return year % 4 == 0
```

-------------------------------------------------


```python
import pytest

@pytest.mark.parametrize("year", [1700, 1800, 1900, 2100, 2200, 2300])
def test_years_divisible_by_100_and_not_by_400_are_leap_years(year):
    assert not is_leap_year(year)

@pytest.mark.parametrize("year", [1600, 2000,2400])
def test_years_divisible_by_400_are_leap_years(year):
    assert is_leap_year(year)

```

-------------------------------------------------

```python
def is_leap_year(year: int) -> bool:
    return (year % 4 == 0
      and year % 100 != 0
      or year % 400 == 0
    )
```

-------------------------------------------------

> “Would you tell me, please, which way I ought to go from here?”
> “That depends a good deal on where you want to get to,” said the Cat.
> “I don’t much care where–” said Alice.
> “Then it doesn’t matter which way you go,” said the Cat.
> “–so long as I get SOMEWHERE,” Alice added as an explanation.
> “Oh, you’re sure to do that,” said the Cat, “if you only walk long enough.”

lewis Carroll - Alice in Wonderland

------------------------------------------------

# A slight digression

## Hoare logic

{P}C{Q}

## BDD

* Given / Arrange
* When  / Act
* Then  / Assert

-------------------------------------------------

# Proofs in C

The following can be automatically verified by Frama-C:

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

-------------------------------------------------

Built up of hoare statements:

```
\valid a+i {int e = a[i];} e == a[i]
```

connected with:

```
    p1 {c1} q , q {c2} r
    -------------------------

        p1 {c1 ; c2 } r
```



-------------------------------------------------


```python
def is_leap_year(year: int) -> bool:
    return (year % 4 == 0
      and year % 100 != 0
      or year % 400 == 0
    )
```

-------------------------------------------------

# mutation testing

* Find code for which mutants are not killed
* Find tests that never kill mutants

-------------------------------------------------

The leap year tests surprisingly kills a surprisingly large amount of mutants:

* `year % 4 == 0 and year % 231 != 0 or year % 400 == 0`
* `year % 4 == 0 or year % 100 != 0 and year % 400 == 0`
* and 10000 more!

-------------------------------------------------

# Automating mutation testing

-------------------------------------------------

# What is Property-based testing (PBT) ?

-------------------------------------------------

# Perspective: PBT is just fuzzing for unit tests

-------------------------------------------------


# What is fuzzing?

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
* AFL++
* Shellshock
* google/oss-fuzz (sqlite3, ffmpeg, openssl)
* Compiler fuzzing

---------------------------------------------------

# How does this relate to property based testing?

Property based testing is fuzzing for unit tests:

```python
from hypothesis import given
import hypothesis.strategies as st

@given(a=st.integers(), b=st.integers())
def test_sum_is_commutative(a, b):
    assert a + b == b + a
```

---------------------------------------------------

# Sorting is permuting


```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(elements=st.integers()))
def test_sorting_results_in_a_permutation(lst):
    sorted_list = sorted(lst)
    for element in lst:
        assert element in sorted_list
    for element in sorted_list:
        assert element in lst
```

---------------------------------------------------

# Sorting orders


```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(elements=st.integers()))
def test_sorting_orders(lst):
    sorted_list = sorted(lst)
    for i in range(len(sorted_list)-1):
        assert sorted_list[i] <= sorted_list[i+1]
```
----------------------------------------------------

# Fizzbuzz

```python
def fizzbuzz(n: int) -> str:
    return "Fizz" * (n % 3 == 0) + "Buzz" * (n % 5 == 0) or str(n)
```

(https://medium.com/codex/one-line-fizzbuzz-solution-in-python-3-9aff0cd98a69)

----------------------------------------------------

```python
import hypothesis.strategies as st

numbers_divisible_by_3 = st.integers().filter(lambda n: n % 3 == 0)
numbers_divisible_by_5 = st.integers().filter(lambda n: n % 5 == 0)
numbers_divisible_by_15 = st.integers().filter(lambda n: n % 15 == 0)
numbers_not_divisible_by_3_nor_5 = st.integers().filter(
    lambda n: n % 3 != 0 and n % 5 != 0
)
```


----------------------------------------------------

```python
import hypothesis.strategies as st

numbers_divisible_by_3 = st.integers().map(lambda n: n * 3)
numbers_divisible_by_5 = st.integers().map(lambda n: n * 5)
numbers_divisible_by_15 = st.integers().map(lambda n: n * 15)
numbers_not_divisible_by_3_nor_5 = st.integers().filter(
    lambda n: n % 3 != 0 and n % 5 != 0
)
```

---------------------------------------------------

```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.integers())
def test_fizzbuzz_is_either_n_fizz_buzz_or_fizzbuzz(n):
    assert fizzbuzz(n) in {str(n), "Fizz", "Buzz", "FizzBuzz"}
```

---------------------------------------------------

```python
from hypothesis import given
import hypothesis.strategies as st

@given(numbers_divisible_by_3.filter(lambda n: n % 5 != 0))
def test_fizzbuzz_returns_fizz(n):
    assert fizzbuzz(n) == "Fizz"
```

---------------------------------------------------

```python
from hypothesis import given
import hypothesis.strategies as st

@given(numbers_divisible_by_5.filter(lambda n: n % 3 != 0))
def test_fizzbuzz_returns_buzz(n):
    assert fizzbuzz(n) == "Buzz"
```

---------------------------------------------------


```python
from hypothesis import given
import hypothesis.strategies as st

@given(numbers_divisible_by_15)
def test_fizzbuzz_returns_fizzbuzz(n):
    assert fizzbuzz(n) == "FizzBuzz"
```

---------------------------------------------------

```python
from hypothesis import given
import hypothesis.strategies as st

@given(numbers_not_divisible_by_3_nor_5)
def test_fizzbuzz_returns_number(n):
    assert fizzbuzz(n) == str(n)
```

---------------------------------------------------

# Example 4: Read/Write roundtrip


```python
import yaml
from hypothesis import given
import hypothesis.strategies as st

@given(st.dictionaries(keys=st.text(), values=st.text()))
def test_reading_and_writing_yaml_are_left_inverse(data):
    assert yaml.load(yaml.dump(data)) == data

```
-----------------------------------------------------------------

* Functions f and g are right-inverse if for all x:A . f(g(x)) = x
* Functions f and g are left-inverse if for all x:A . g(f(x)) = x
* f and g are inverse if they are both right-inverse and left-inverse.
* yaml.dump and yaml.load are inverse functions.

---------------------------------------------------------------


# Do I really need hypothesis? Why not just rand and loop?

* Killer feature: shrinking
* Reproducing failures
* Checking for flakiness
* Tuning the number/size of examples
* CI logs
* Complicated data

--------------------------------------------------------------

# Shrinking

```python
from hypothesis import given
import hypothesis.strategies as st

def average(numbers: list[float]):
    return sum(numbers) / len(numbers)


@given(st.lists(st.floats()))
def test_that_average_does_not_exceed_max(numbers):
    assert max(numbers) >= average(numbers)
```

----------------------------------------------------

```python
@given(st.lists(st.floats(), min_size=1))
def test_that_average_does_not_exceed_max(numbers):
    assert max(numbers) >= average(numbers)
```

-----------------------------------------------------

```python
@given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
def test_that_average_does_not_exceed_max(numbers):
    assert max(numbers) >= average(numbers)
```

-----------------------------------------------------

```
237595.00000000006 = max([237595.00000000006, 237595.00000000006, 237595.00000000006])
237595.0000000001 = average([237595.00000000006, 237595.00000000006, 237595.00000000006])
```

-----------------------------------------------------


# Shrinking

```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
def test_that_average_does_not_exceed_max(numbers):
    print(numbers, success)
    assert max(numbers) >= average(numbers)
```

------------------------------------------------------

```
[0.0] True
[0.0] True
[1.5, -2.5353189122290976e-107, 1.1754943508222875e-38, -1.1] True
...
[-1.192092896e-07, 3.402823466e+38,..., 1.7976931348623157e+308] False # 23 elemens
[-9007199254740992.0, 2.225073858507e-311] True
[-2.2250738585072014e-308, ..., 1.7976931348623155e+308] False # 11 elements
[1.5, -0.99999, 1.401298464324817e-45, 2.2250738585072014e-308] True
[1.9, ..., 6.103515625e-05] True
...
# 41 more iterations
[1.7976931348623157e+308, 1.7976931348623157e+308] False
[1.7976931348623157e+308] True
...
# 20 more iteration attempting 1 and 2 element lists
[1.7976931348623153e+308, 1.7976931348623157e+308] False
[1.797693134862315e+308, 1.7976931348623157e+308] False
[1.7976931348623145e+308, 1.7976931348623157e+308] False
...
# 200 more iterations trying more 1 and 2 element lists
[9.9792015476736e+291, 1.7976931348623157e+308] False
```

-------------------------------------------------------------

# But what if what I am trying to generate is complicated?

. . .

Enter

. . .

`hypothesis.strategies.composite`

-------------------------------------------------------------

# Example 5: generator for lines

```python
from dataclasses import dataclass

@dataclass
class Point:
    x: float
    y: float
    z: float

@dataclass
class Line:
    start: Point
    end: Point
```

--------------------------------------------------------

```python
import hypothesis.strategies as st
from point import Point
from line import Line

coordinates = st.floats(allow_nan=False, allow_infinity=False)
points = st.builds(Point, coordinates, coordinates)
lines = st.builds(Line, points, points)
````

. . .

But what if I want to create some triangles?

--------------------------------------------------------------

```python
import hypothesis.strategies as st
from hypothesis import assume

@st.composite
def triangles(draw):
    point1 = draw(points)
    point2 = draw(points)
    point3 = draw(points)

    assume(is_affine_independent([point1, point2, point3]))

    return (Line(point1, point2), Line(point2, point3), Line(point3, point1))
```

-------------------------------------------

# Where do I find more?

* hypothesis.works
* hypothesis.works/articles/quickcheck-in-every-language/

-------------------------------------------

Thank you!
