        .. _3d-lang:

The 3d Dependent Data Description language
==========================================

3d supports (nested) structs, constraints, enums, parameterized data
types, tagged or otherwise value-dependent unions, fixed-size arrays,
and variable-size arrays. In addition to data validation, 3d also
supports *local actions* to pass values read from the data structure,
or pointers to them, to the caller code.

Structs
-------

We would like to extract a validator for a simple point type, with X
and Y coordinates. So we create a file, ``HelloWorld.3d``, with the
following 3d data format description:

.. literalinclude:: HelloWorld.3d
    :language: c

This data format is very similar to a C type description, where
``UINT16`` denotes the type of unsigned 16-bit integers, represented
as little-endian; with the addition of the ``entrypoint`` keyword,
which tells 3d to expose a validator to the final user.

Once we run ``3d`` with this file, we obtain several files:

* ``HelloWorld.c`` and ``HelloWorld.h``, which contain the actual verified
  validators;

* ``HelloWorldWrapper.c`` and ``HelloWorldWrapper.h``, which contain
  entrypoint function definitions for data validators that the user
  should ultimately use in their client code. More precisely, here is
  the contents of ``HelloWorldWrapper.h``:

.. literalinclude:: HelloWorldWrapper.h
    :language: c
    :start-after: SNIPPET_START: Point
    :end-before: SNIPPET_END: Point

The ``HelloWorldCheckPoint`` function is the actual validator for the
``point`` type. It takes an array of bytes, ``base``, and its length
``len``, and it returns 1 if ``base`` starts with valid ``point`` data
that fits in ``len`` bytes or less, and 0 otherwise.

More generally, for a given ``Module.3d``, a type definition ``typ``
marked with ``entrypoint`` tells 3d to expose its validator in
``ModuleWrapper.h`` which will bear the name ``ModuleCheckTyp``.

Structs can be nested, such as in the following instance:

.. literalinclude:: Triangle.3d
    :language: c

Then, since in this file the definition of ``point`` is not prefixed
with ``entrypoint``, only ``triangle`` will have its validator exposed
in ``TriangleWrapper.h``.

There can be several definitions marked ``entrypoint`` in a given
``.3d`` file.

.. warning::

  3d does not enforce any alignment constraints, and does not
  introduce any implicit alignment padding. So, for instance, in the
  following data format description:

  .. literalinclude:: ColoredPoint.3d
      :language: c

  * in ``coloredPoint1``, 3d will not introduce any padding between
    the ``color`` field and the ``pt`` field;

  * in ``coloredPoint2``, 3d will not introduce any padding after the
    ``color`` field.

Constraints
-----------

Validators for structs alone are only layout-related. Beyond that, 3d
provides a way to actually check for constraints on their field
values:

.. literalinclude:: Smoker.3d
    :language: c

In this example, the validator for ``smoker`` will check that the
value of the ``age`` field is at least 21.

.. note::

  (FIXME) Integer constants are currently considered to be 32-bit
  integers; 3d does not support any kind of type casting at this time.

The constraint language includes integer arithmetic (``+``, ``-``,
``*``, ``/``, ``==``, ``!=``, ``<=``, ``<``, ``>=``, ``>``) and
Boolean propositional logic (``&&``, ``||``, ``!``)

Constraints on a field can also depend on the values of the previous
fields of the struct. For instance, here is a type definition for a
pair ordered by increasing values:

.. literalinclude:: OrderedPair.3d
    :language: c

.. warning::

   Arithmetics on constraints are evaluated in machine integers, not
   mathematical integers. Thus, the following naive definition:

   .. literalinclude:: BoundedSumConst.3d
       :language: c
       :start-after: SNIPPET_START: boundedSumNaive
       :end-before: SNIPPET_END: boundedSumNaive

   will fail at F* verification because the ``left + right`` sum must
   be proven to not overflow *before* evaluating the condition. The
   correct way of stating the condition is as follows:

   .. literalinclude:: BoundedSumConst.3d
       :language: c
       :start-after: SNIPPET_START: boundedSumCorrect
       :end-before: SNIPPET_END: boundedSumCorrect

   which is correct because the right-hand-side condition of a ``&&``
   is evaluated in a context where the left-hand-side can be assumed
   to be true (thus ``42 - left`` will not underflow.)

Bitfields
---------

TODO:

* What is the constraint on a bitfield type? on field sizes?

* Can constraints be put on indvidual fields of a bitfield? 


Constants and Enumerations
--------------------------

3d provides a way to define numerical constants:

.. literalinclude:: ConstColor.3d
    :language: c

Alternatively, 3d provides a way to define enumerated types:

.. literalinclude:: Color.3d
    :language: c

Then, the validator for ``coloredPoint`` will check that the value of
``col`` is either 1, 2 (for ``green``), or 42.

Contrary to structs, enum types cannot be marked ``entrypoint``.

The first enum label must be associated with a value.

The support type (here ``UINT32``) must be the same type as the type
of the values associated to each label.

.. note::

  (FIXME) Contrary to type definitions, enum definitions must not be
  followed by a ``;``

Parameterized data types
------------------------

3d also offers the possibility to parameterize a data type description
with arguments that can then be reused in constraints. For instance,
the following ``BoundedSum.3d`` data description defines a pair of two
integers whose sum is bounded by a bound provided by the user as
argument:

.. literalinclude:: BoundedSum.3d
    :language: c
    :start-after: SNIPPET_START: boundedSum
    :end-before: SNIPPET_END: boundedSum

Then, these arguments will add up to the arguments of the
corresponding validator in the ``BoundedSumWrapper.h`` header produced
by 3d:

.. literalinclude:: BoundedSumWrapper.h
    :language: c
    :start-after: SNIPPET_START: BoundedSum
    :end-before: SNIPPET_END: BoundedSum

Parameterized data types can also be instantiated within the ``.3d``
file itself, including by the value of the field of a struct:

.. literalinclude:: BoundedSum.3d
    :language: c
    :start-after: SNIPPET_START: mySum
    :end-before: SNIPPET_END: mySum

A parameterized data type can also check whether a condition on its
arguments holds before even trying to check its contents:

.. literalinclude:: BoundedSumWhere.3d
    :language: c

Tagged unions
-------------

3d supports *tagged unions*: a data type can store a value named *tag*
and a *payload* whose type depends on the tag value.

For instance, the following description defines the type of an integer
prefixed by its size in bits.

.. literalinclude:: TaggedUnion.3d
    :language: c

.. note::

  (FIXME) Currently, union cases can only be introduced by constants
  defined with ``#define``. Due to current restrictions on
  double-fetches, 3d currently does not support unions tagged by enum
  values.

.. warning::

  3d does not enforce that all cases of a union be of the same size,
  and 3d does not introduce any implicit padding to enforce it. Nor
  does 3d introduce any alignment padding.

A ``casetype`` type actually defines an untagged union type dependent
on an argument value, which can be reused, e.g. for several types that
put different constraints on the value of the tag.

A ``casetype`` type can also be marked ``entrypoint``.

Element-sized arrays
--------------------

3d lets the user define arrays with a constant number of elements. The
following example defines a triangle where the three corners of the
triangle are recorded in an array of 3 elements:

.. literalinclude:: Triangle2.3d
    :language: c

.. note::

  (FIXME) There is no direct 3d support for arrays with a variable
  number of elements. Sometimes, but not always, they can be simulated
  with variable-size arrays in terms of size in bytes.


Byte-sized arrays
-----------------

3d lets the user define arrays with a constant of variable size in bytes.

TODO:

* ``suffix``: am I restricted to only one explicitly declared
  variable-sized array having to be named ``suffix`` and be the last
  element of my struct? does it mean that if I need several
  variable-sized arrays, I have to use parameterized data types?

* ``sizeof``: how does it work with "variable-size" types with no
  variable-size suffix? (e.g. unions where cases do not have the same
  size)

* how could we define variable-length arrays in terms of number of
  elements?

Actions
-------

TODO:

* how to return values as pointer arguments

* ``onerror``: does it work?

* how do actions work with array elements

Comments
--------

The user can insert comments in their ``.3d`` file, some of which will
be inserted into the ``.c`` file:

TODO
