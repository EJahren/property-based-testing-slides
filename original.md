---
title: "Property based testing: fresh out of the ivory tower"
author: Eivind Jahren
date: "may 2019"
...

# What?


Way to Organize Test Data


Fuzzing for Unit Tests

Fuzzing highlights:

* AFL (nginx, man, firefox)
* Shellshock
* google/oss-fuzz (sqlite3, ffmpeg, openssl)

|Generators             | Properties |
--------------------------------------
| How is data Generated | Gurantees between data and code |
|"How to generate odd numbers" |"Given two even numbers the sum of these is even" |
-----------------------------------------------------------------------------------

# Why?


Unit Test or Property? Both!


Any unit test can be written
as a property.

```python
@given(just([3,2,1,4]))
def test_sort(list):
    self.assertEqual(sort(list), [1,2,3,4])
```


```python
@given(lists(elements=integers(min_value=5)))
def test_sort(list):
    sorted = sort(list + [3,2,1,4])
    self.assertEqual(sort[0:3], [1,2,3,4])
```


# Roll your own? Maybe not...


* Scaling of samples
* Recover Counterexamples
* Start Debug on Failing Case
* Fix seed
* Minimizing counterexamples

# Goes well with Test First!


> Write the smallest property that describes
> the most essential behavior.


> If it is difficult to generate, its difficult
> to use.

