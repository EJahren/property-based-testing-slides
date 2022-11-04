from dataclasses import dataclass


@dataclass(order=True)
class Person:
    lastname: str
    firstname: str
