import hypothesis.strategies as st
from hypothesis import given


def chop(element: int, lst: list[int]) -> int:
    ...


@given(st.integers(), st.lists(st.integers())):
def test_chop_base_case(element, lst):
    if element not in lst:
        assert chop(element, lst) == -1
    else:
        assert element[chop(element, lst)] == element
