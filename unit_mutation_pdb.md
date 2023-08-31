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

* Getting back to our roots
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

> »System testing should be automated as well. A collection of executable
> programs should be produced and maintained to exercise all parts of the
> system. The set should be open ended and maintenance utilities should be
> included

- NATO SOFTWARE ENGINEERING CONFERENCE 1968

-------------------------------------------------

Simple Testing Can Prevent Most Critical Failures
An Analysis of Production Failures in Distributed Data-Intensive Systems
usenix.org/system/files/conference/osdi14/osdi14-paper-yuan.pdf

-------------------------------------------------

> A majority of the production failures (77%) can be reproduced by a unit test.

usenix.org/system/files/conference/osdi14/osdi14-paper-yuan.pdf


# Power Peg (Knights Captal Group failure)

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

# How do we want this to go ideally?


> To be a leap year, the year number must be divisible by four – except for
> years divisble by 100, unless they are also be divisible by 400.


-------------------------------------------------

```python
import pytest

@pytest.mark.parametrize("year", [1939, 1945, 1997, 1999])
def test_only_years_divisible_by_four_are_leap_years(year):
    assert not is_leap_year(year)
```

-------------------------------------------------

```python
    def is_leap_year(year:int) -> bool:
        return False
```

-------------------------------------------------


```python
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
@pytest.mark.parametrize("year", [1600, 1700, 1800, 1900, 2000])
def test_years_divisible_by_100_are_not_leap_years_unless_divisible_by_400(year):
    assert not is_leap_year(year) or year % 400 == 0

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

[](!coverage.png)

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

# Another Example: Sorting is permuting


```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(elements=st.integers()))
def test_sorting_results_in_permutation(lst):
    sorted_list = sorted(lst)
    for element in lst:
        assert element in sorted_list
    for element in sorted_list:
        assert element in lst
```

---------------------------------------------------

# Example 3: Sorting orders


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

# Lets compare with a unit test

```python
def test_sorting():
    assert sorted([]) == []
    assert sorted([1]) == [1]
    assert sorted([1,3,2]) == [1, 2, 3]
    assert sorted(['b','b','b','a']) == ['a', 'b', 'b', 'b']
```

----------------------------------------------------

# Accidental coupling

```python
from dataclasses import dataclass


@dataclass(order=True)
class Person:
    lastname: str
    firstname: str


def test_sorting():
    assert sorted(
        [Person("Bell", "Bert"), Person("Armstrong", "Amanda")]
    ) == [ Person("Armstrong", "Amanda"), Person("Bell", "Bert")]

```

. . .

what happens if we want to change to:

```python
from enum import Enum
from dataclasses import dataclass

class Role(Enum):
    ...

@dataclass(order=True)
class Person:
    role: Role
    lastname: str
    firstname: str
```


---------------------------------------------------


```python
from hypothesis import given
import hypothesis.strategies as st

from person import Person

persons = st.builds(Person)
orderables = st.one_of(persons, st.integers())

@given(st.lists(elements=orderables))
def test_sorting_orders(list):
    ...
```

---------------------------------------------------

# Example 4: Read/Write roundtrip


```python
import yaml
from io import StringIO
from hypothesis import given
import hypothesis.strategies as st

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
