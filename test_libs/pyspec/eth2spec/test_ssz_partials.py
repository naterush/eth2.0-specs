from utils.ssz.ssz_typing import *
from utils.ssz.ssz_impl import *
from utils.ssz.ssz_partials import *
import os, random

class Person(Container):
    is_male: bool
    age: uint64
    name: bytes

class City(Container):
    coords: Vector[uint64, 2]
    people: List[Person]

people = [
    Person(is_male=True, age=45, name=b"Alex"),
    Person(is_male=True, age=47, name=b"Bob"),
    Person(is_male=True, age=49, name=b"Carl"),
    Person(is_male=True, age=51, name=b"Danny"),
    Person(is_male=True, age=53, name=b"Evan"),
    Person(is_male=False, age=55, name=b"Fae"),
    Person(is_male=False, age=57, name=b"Ginny"),
    Person(is_male=False, age=59, name=b"Heather"),
    Person(is_male=False, age=61, name=b"Ingrid"),
    Person(is_male=False, age=63, name=b"Kane"),
]

city = City(coords=Vector[uint64, 2](45, 90), people=people)

paths = [
    ["coords", 0],
    ["people", 4, "name", 1],
    ["people", 9, "is_male"],
    ["people", 7],
    ["people", 1],
]

full = ssz_partial(City, ssz_full(city))
print(full.ssz_partial.objects.keys())
for path in paths:
    print(path, list(full.ssz_partial.access_partial(path).objects.keys()))
    # print(path, get_nodes_along_path(full, path, typ=City).keys())
p = merge(*[full.ssz_partial.access_partial(path) for path in paths])
object_keys = sorted(list(p.ssz_partial.objects.keys()))[::-1]
# p = SSZPartial(infer_type(city), branch2)
assert p.coords[0] == city.coords[0]
assert p.coords[1] == city.coords[1]
assert len(p.coords) == len(city.coords)
assert p.coords.hash_tree_root() == hash_tree_root(city.coords)
assert p.people[4].name[1] == city.people[4].name[1]
assert len(p.people[4].name) == len(city.people[4].name)
assert p.people[9].is_male == city.people[9].is_male
assert p.people[7].is_male == city.people[7].is_male
assert p.people[7].age == city.people[7].age
assert p.people[7].name[0] == city.people[7].name[0]
assert str(p.people[7].name) == str(city.people[7].name)
assert str(p.people[1]) == str(city.people[1])
assert p.people[1].name.hash_tree_root() == hash_tree_root(city.people[1].name)
assert p.hash_tree_root() == hash_tree_root(city)
print("Reading tests passed")
p.people[7].age = 20
city.people[7].age = 20
assert p.people[7].age == 20
assert p.hash_tree_root() == hash_tree_root(city)
p.coords[1] = 100
city.coords[1] = 100
assert p.hash_tree_root() == hash_tree_root(city)
p.people[1] = Person(is_male=False, age=30, name=b"Betty")
city.people[1] = Person(is_male=False, age=30, name=b"Betty")
assert p.hash_tree_root() == hash_tree_root(city)
print(hash_tree_root(city))
print("Writing tests passed")
