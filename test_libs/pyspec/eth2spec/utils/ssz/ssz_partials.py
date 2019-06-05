from ..merkle_minimal import hash, next_power_of_two
from .ssz_typing import *
from .ssz_impl import *

ZERO_CHUNK = b'\x00' * 32

def last_power_of_two(x):
    return next_power_of_two(x+1) // 2

def concat_generalized_indices(x, y):
    return x * last_power_of_two(y) + y - last_power_of_two(y)

def rebase(objs, new_root):
    return {concat_generalized_indices(new_root, k): v for k,v in objs.items()}

def constrict_generalized_index(x, q):
    depth = last_power_of_two(x // q)
    o = depth + x - q * depth
    if concat_generalized_indices(q, o) != x:
        return None
    return o

def is_generalized_index_child(c, a):
    return False if c < a else True if c == a else is_generalized_index_child(c // 2, a)

def unrebase(objs, q):
    o = {}
    for k,v in objs.items():
        new_k = constrict_generalized_index(k, q)
        if new_k is not None:
            o[new_k] = v
    return o

def filler(starting_position, chunk_count):
    at, skip, end = chunk_count, 1, next_power_of_two(chunk_count)
    value = ZERO_CHUNK
    o = {}
    while at < end:
        while at % (skip*2) == 0:
            skip *= 2
            value = hash(value + value)
        o[(starting_position + at) // skip] = value
        at += skip
    return o

def merkle_tree_of_chunks(chunks, root):
    starting_index = root * next_power_of_two(len(chunks))
    o = {starting_index+i: chunk for i,chunk in enumerate(chunks)}
    o = {**o, **filler(starting_index, len(chunks))}
    return o

@infer_input_type
def ssz_leaves(obj, typ=None, root=1):
    if is_list_kind(typ):
        o = {root * 2 + 1: len(obj).to_bytes(32, 'little')}
        base = root * 2
    else:
        o = {}
        base = root
    if is_bottom_layer_kind(typ):
        data = serialize_basic(obj, typ) if is_basic_type(typ) else pack(obj, read_elem_type(typ))
        q = {**o, **merkle_tree_of_chunks(chunkify(data), base)}
        #print(obj, root, typ, base, list(q.keys()))
        return(q)
    else:
        fields = get_typed_values(obj, typ=typ)
        sub_base = base * next_power_of_two(len(fields))
        for i, (elem, elem_type) in enumerate(fields):
            o = {**o, **ssz_leaves(elem, typ=elem_type, root=sub_base+i)}
        q = {**o, **filler(sub_base, len(fields))}
        #print(obj, root, typ, base, list(q.keys()))
        return(q)

@infer_input_type
def ssz_full(obj, typ=None):
    return fill(ssz_leaves(obj, typ=typ))

def get_basic_type_size(typ):
    if is_uint_type(typ):
        return uint_byte_size(typ)
    elif is_bool_type(typ):
        return 1
    else:
        raise Exception("Type not basic: {}".format(typ))

def get_bottom_layer_element_position(typ, base, length, index):
    """
    Returns the generalized index and the byte range of the index'th value
    in the list with the given base generalized index and given length
    """
    L = 1 if is_basic_type(typ) else length
    if index >= L:
        raise IndexError("list index {} out of range (length {})".format(index, L))
    elem_typ = typ if is_basic_type(typ) else read_elem_type(typ)
    elem_size = get_basic_type_size(elem_typ)
    chunk_index = index * elem_size // 32
    chunk_count = (1 if is_basic_type(typ) else length) * elem_size // 32
    generalized_index = base * next_power_of_two(chunk_count) + chunk_index
    start = elem_size * index % 32
    return generalized_index, start, start+elem_size

@infer_input_type
def descend(obj, path, typ=None):
    for p in path:
        if isinstance(p, int):
            if obj is not None:
                obj = obj[p]
            typ = read_elem_type(typ)
        elif p == '__len__':
            if obj is not None:
                obj = len(obj)
            typ = uint64
        elif isinstance(p, str):
            if obj is not None:
                obj = getattr(obj, p)
            typ = typ.get_fields_dict()[p]
        else:
            raise Exception("Unknown path element {}".format(p))
    return obj, typ

def get_branch_indices(tree_index):
    o = [tree_index ^ 1]
    while o[-1] > 1:
        o.append((o[-1] // 2) ^ 1)
    return o[:-1]

def fill(objects):
    objects = {k:v for k,v in objects.items()}
    keys = sorted(objects.keys())[::-1]
    pos = 0
    while pos < len(keys):
        k = keys[pos]
        if k in objects and k^1 in objects and k//2 not in objects:
            objects[k//2] = hash(objects[k&-2] + objects[k|1])
            keys.append(k // 2)
        pos += 1
    return objects

def remove_redundant_indices(obj):
    return {k:v for k,v in obj.items() if not (k*2 in obj and k*2+1 in obj)}

def merge(*args):
    o = {}
    for arg in args:
        assert arg.typ == args[0].typ
        o = {**o, **arg.objects}
    return ssz_partial(args[0].typ, remove_redundant_indices(fill(o)))

class OutOfRangeException(Exception):
    pass

class SSZPartial():
    def __init__(self, typ, objects):
        assert not is_basic_type(typ)
        self.objects = objects
        self.typ = typ

    def access_partial(self, path):
        gindex = self.get_generalized_index(path)
        branch_indices = {k: self.objects[k] for k in get_branch_indices(gindex)}
        _, bottom_typ = descend(None, path, typ=self.typ)
        if is_basic_type(bottom_typ):
            leaf_indices = {gindex: self.objects[gindex]}
        else:
            leaf_indices = ssz_leaves(self.execute_path(path), typ=bottom_typ, root=gindex)
        return SSZPartial(self.typ, {**branch_indices, **leaf_indices})

    def merge(self, target):
        assert self.typ == target.typ
        return SSZPartial(self.typ, {**self.objects, **target.objects})

    def get_generalized_index(self, path):
        root = 1
        typ = self.typ
        for p in path:
            if p == '__len__':
                return root * 2 + 1 if is_list_kind(typ) else None
            base = root * 2 if is_list_kind(typ) else root
            length = (
                1 if is_basic_type(typ) else typ.length if is_vector_kind(typ) else
                len(typ.get_field_names()) if is_container_type(typ) else int.from_bytes(self.objects[root * 2 + 1], 'little')
            )
            if is_bottom_layer_kind(typ):
                root, _, _ = get_bottom_layer_element_position(typ, base, length, p)
            else:
                if is_container_type(typ):
                    index = typ.get_field_names().index(p)
                    typ = typ.get_field_types()[index]
                elif is_vector_kind(typ) or is_list_kind(typ):
                    index, typ = p, read_elem_type(typ)
                else:
                    raise Exception("Unknown type: {}".format(typ))
                root = base * next_power_of_two(length) + index
        return root

    def execute_path(self, path):
        tree_index = self.get_generalized_index(path)
        if tree_index is None and path[-1] == '__len__':
            _, bottom_typ = descend(None, path[:-1], typ=self.typ)
            return bottom_typ.length
        _, bottom_typ = descend(None, path, typ=self.typ)
        if is_basic_type(bottom_typ):
            basic_type_size = get_basic_type_size(bottom_typ)
            bottom_index = path[-1] if path and isinstance(path[-1], int) else 0
            start = bottom_index * basic_type_size % 32
            return deserialize_basic(self.objects[tree_index][start:start+basic_type_size], bottom_typ)
        elif is_list_kind(bottom_typ):
            L = self.execute_path(path+['__len__'])
            o = [self.execute_path(path+[i]) for i in range(L)]
            return bytes(o) if is_bytes_type(bottom_typ) else o
        elif is_vector_kind(bottom_typ):
            o = bottom_typ(*(self.execute_path(path+[i]) for i in range(bottom_typ.length)))
            return bytes(o) if is_bytesn_type(bottom_typ) else o
        elif is_container_type(bottom_typ):
            return bottom_typ(**{field: self.execute_path(path+[field]) for field in bottom_typ.get_field_names()})
        else:
            raise Exception("Unrecognized type")

    def set_path(self, path, value):
        tree_index = self.get_generalized_index(path)
        if tree_index is None and path[-1] == '__len__':
            raise Exception("Cannot set length")
        _, bottom_typ = descend(None, path, typ=self.typ)
        if is_basic_type(bottom_typ):
            basic_type_size = get_basic_type_size(bottom_typ)
            bottom_index = path[-1] if path and isinstance(path[-1], int) else 0
            start = bottom_index * basic_type_size % 32
            self.objects[tree_index] = (
                self.objects[tree_index][:start] +
                serialize_basic(value, bottom_typ) +
                self.objects[tree_index][start+basic_type_size:]
            )
        else:
            for k in list(self.objects.keys()):
                if is_generalized_index_child(k, tree_index):
                    del self.objects[k]
            new_keys = ssz_leaves(value, typ=bottom_typ, root=tree_index)
            for k, v in new_keys.items():
                self.objects[k] = v
        v = tree_index // 2
        while v:
            if v not in self.objects:
                break
            self.objects[v] = hash(self.objects[v * 2] + self.objects[v * 2 + 1])
            v //= 2

class SSZPartialPointer():
    def __init__(self, ssz_partial, path, typ):
        self.ssz_partial = ssz_partial
        self.path = path
        self.typ = typ

    def getter(self, index):
        _, elem_type = descend(None, [index], typ=self.typ)
        if is_basic_type(elem_type):
            return self.ssz_partial.execute_path(self.path + [index])
        else:
            return mk_ssz_pointer(self.ssz_partial, self.path + [index], elem_type)

    def setter(self, index, value):
        self.ssz_partial.set_path(self.path + [index], value)

    def __len__(self):
        return self.getter('__len__')

    def __getitem__(self, index):
        return self.getter(index)

    def __setitem__(self, index, value):
        return self.setter(index, value)

    def __iter__(self):
        return (self[i] for i in range(len(self)))

    def full_value(self):
        if is_bytes_type(self.typ) or is_bytesn_type(self.typ):
            return bytes([self.getter(i) for i in range(len(self))])
        elif is_list_kind(self.typ):
            return [self[i] for i in range(len(self))]
        elif is_vector_kind(self.typ):
            return self.typ(*(self[i] for i in range(len(self))))
        elif is_container_type(self.typ):
            full_value = lambda x: x.full_value() if hasattr(x, 'full_value') else x
            return self.typ(**{field: full_value(self.getter(field)) for field in self.typ.get_field_names()})
        elif is_basic_type(self.typ):
            return self.getter(0)
        else:
            raise Exception("Unsupported type: {}".format(self.typ))

    def hash_tree_root(self):
        o = {k:v for k,v in self.ssz_partial.objects.items() if is_generalized_index_child(k, self.root)}
        keys = sorted(o.keys())[::-1]
        pos = 0
        while pos < len(keys):
            k = keys[pos]
            if k in o and k^1 in o and k//2 not in o:
                o[k//2] = hash(o[k&-2] + o[k|1])
                keys.append(k // 2)
            pos += 1
        return o[self.root]

    def __str__(self):
        return str(self.full_value())

    @property
    def root(self):
        return self.ssz_partial.get_generalized_index(self.path)

def ssz_partial(typ, objects, path=None):
    return mk_ssz_pointer(SSZPartial(typ, objects), path or [], typ)

def mk_ssz_pointer(partial, path, typ):
    ssz_type = (
        Container if is_container_type(typ) else
        typ if (is_vector_type(typ) or is_bytesn_type(typ)) else object
    )
    class Pointer(SSZPartialPointer, ssz_type):
        pass
    if is_container_type(typ):
        Pointer.__annotations__ = typ.__annotations__
        for f in typ.get_field_names():
            getter = (lambda arg: lambda self: self.getter(arg))(f)
            setter = (lambda arg: lambda self, value: self.setter(arg, value))(f)
            setattr(Pointer, f, property(getter, setter))
    return Pointer(partial, path or [], typ)
