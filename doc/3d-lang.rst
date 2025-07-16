.. _3d-lang:

Overview
---------

3d supports several fixed-width integer base types, (nested) structs,
constraints, enums, parameterized data types, tagged or otherwise
value-dependent unions, fixed-size arrays, and variable-size arrays.

In addition to data validation, 3d also supports *local actions* to pass values
read from the data structure, or pointers to them, to the caller code.

3d also supports validating structures that contain pointers, probing pointers
for validity and traversing them in order to validate the data they refer to. 


Base types
----------

The primitive types in 3d include unsigned integers of the following
flavors:

* ``UINT8``: 8-bit unsigned little-endian integer
* UINT16: 16-bit unsigned little-endian integer

  - Literal values of ``UINT8`` are integers with the ``uy`` suffix, e.g.,
    ``0uy, 8uy 255uy`` etc.
    
  - Literals can also be specified in hexadecimal, with hex digits in either
    lower or upper case``0xabuy, 0x1Auy, 0xFFuy, 0xFfuy`` etc.
  - Literal values of ``UINT8`` are integers with the ``uy`` suffix, e.g.,
    ``0uy, 8uy 255uy`` etc.
    
  - Literals can also be specified in hexadecimal, e.g., ``0xabuy, 0xffuy`` etc.


* UINT32: 32-bit unsigned little-endian integer
* UINT64: 64-bit unsigned little-endian integer

Literal values of unsigned integer types can be specified in either decimal or
hexadecimal, e.g., ``0, 1, 255`` etc. in decimal; or in with hexadecimal with 
either lower or upper case, e.g., ``0x0, 0x01, 0xff, 0xFF, 0xFf`` etc.

3d infers the smallest width of a literal based on type information, but the
width can also be specified explicitly.

For ``UINT8``, a literal has the ``uy`` suffix, e.g., ``0uy, 1uy, 0xffuy,
255uy`` etc.

For ``UINT16``, a literal has the ``us`` suffix, e.g., ``0us, 1us, 0xffffus,
255us, 65535us`` etc.

For ``UINT32``, a literal has the ``ul`` suffix, e.g., ``0ul, 1ul, 0xfffffffful,
255ul, 4294967295ul`` etc.

For ``UINT64``, a literal has the ``uL`` suffix, e.g., ``0uL, 1uL, 0xffffffffffffffffuL,
255uL`` etc.

We also provide big-endian unsigned integers:

* UINT16BE: 16-bit unsigned big-endian integer
* UINT32BE: 32-bit unsigned big-endian integer
* UINT64BE: 64-bit unsigned big-endian integer

Big-endian integers are often useful in describing network message formats. 3d
ensures suitable endianness conversions are applied when comparing or equating
integers represented in different endianness. We show an example of this
:ref:`below <sec-constraints>`.

Structs
-------

We would like to extract a validator for a simple point type, with X
and Y coordinates. So we create a file, ``HelloWorld.3d``, with the
following 3d data format description:

.. literalinclude:: HelloWorld.3d
    :language: 3d

This data format is very similar to a C type description, where
``UINT16`` denotes the type of unsigned 16-bit integers, represented
as little-endian; with the addition of the ``entrypoint`` keyword,
which tells 3d to expose the validator for the type to the final user.

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
    :language: 3d

Then, since in this file the definition of ``point`` is not prefixed
with ``entrypoint``, only ``triangle`` will have its validator exposed
in ``TriangleWrapper.h``.

There can be multiple definitions marked ``entrypoint`` in a given
``.3d`` file.

.. warning::

  By default, 3d does not enforce any alignment constraints, and does not
  introduce any implicit alignment padding. So, for instance, in the following
  data format description:

  .. literalinclude:: ColoredPoint.3d
      :language: 3d

  * in ``coloredPoint1``, 3d will not introduce any padding between
    the ``color`` field and the ``pt`` field;

  * in ``coloredPoint2``, 3d will not introduce any padding after the
    ``color`` field.

  This is in the spirit of keeping 3d specifications explicit. However, 3d does
  support an option to add alignment padding to a structure, as described
  :ref:`below <sec-alignment>`.


.. _sec-constraints:

Constraints
-----------

Validators for structs alone are only layout-related. Beyond that, 3d
provides a way to actually check for constraints on their field
values:

.. literalinclude:: Smoker.3d
    :language: 3d

In this example, the validator for ``smoker`` will check that the
value of the ``age`` field is at least 21.

The constraint language includes integer arithmetic (``+``, ``-``,
``*``, ``/``, ``==``, ``!=``, ``<=``, ``<``, ``>=``, ``>``) and
Boolean propositional logic (``&&``, ``||``, ``!``)

Constraints on a field can also depend on the values of the previous
fields of the struct. For instance, here is a type definition for a
pair ordered by increasing values:

.. literalinclude:: OrderedPair.3d
    :language: 3d

.. warning::

   Arithmetics on constraints are evaluated in machine integers, not
   mathematical integers. Thus, the following naive definition:

   .. literalinclude:: BoundedSumConst.3d
       :language: 3d
       :start-after: SNIPPET_START: boundedSumNaive
       :end-before: SNIPPET_END: boundedSumNaive

   will fail at F* verification because the expression ``left + right``
   must be proven to not overflow *before* evaluating the condition. The
   correct way of stating the condition is as follows:

   .. literalinclude:: BoundedSumConst.3d
       :language: 3d
       :start-after: SNIPPET_START: boundedSumCorrect
       :end-before: SNIPPET_END: boundedSumCorrect

   This verifies because F* evaluates the right-hand-side
   condition of a ``&&`` in a context where the left-hand-side
   condition is assumed to be true (thus ``42 - left`` will not underflow.)

Bitfields
---------

Like in C, the fields of a struct type in 3d can include bitfields,
i.e., unsigned integer types of user-specified width represented
packed within unsigned integer fields of the canonical sizes
UINT16, UINT32 and UINT64.

Consider the following example:

.. literalinclude:: BF.3d
    :language: 3d
    :start-after: SNIPPET_START: BF
    :end-before: SNIPPET_END: BF

This defines a struct ``BF`` occupying 32 bits of memory, where the
first 6 bits are for the field ``x``; the next 10 bits are for the
field ``y``; and the following 16 bits are for the field ``z``.

The fields ``x``, ``y``, and ``z`` can all be used in specifications
and are implicitly promoted to the underlying integer type, ``UINT32``
in this case, although the 3d verifier is aware of suitable bounds on
the types, e.g., that ``0 <= x < 64``.

For types ``UINT8``. ``UINT16``, ``UINT32`` and ``UINT64``, 3d
implements `MSVC's rules for packing bit fields
<https://learn.microsoft.com/en-us/cpp/c-language/c-bit-fields>`_:
least-significant bit first. For instance:

.. literalinclude:: BF.3d
    :language: 3d
    :start-after: SNIPPET_START: BF2
    :end-before: SNIPPET_END: BF2

In ``BF2``, although ``x``, ``y`` and ``z`` cumulatively consume only
26 bits, the layout of ``BF2`` is actually as shown below, consuming
40 bits, since a given field must be represented within the bounds of
a single underlying type---we have 10 unused bits before ``x`` and 4
unused bits before ``y``.

.. code-block:: text

   counting from most-significant bits to least-significant bits:

    0                   1                   2                   3                   4
    0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-
   |      Unused       |     x     | Unused|           y           |        z      |
   |                   |           |       |                       |               |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-

EverParse version 2023.04.17 and beyond encode bitfields with
big-endian integer types ``UINT16BE``, ``UINT32BE`` and ``UINT64BE``
with the most-significant bit (MSB) first, which is necessary for many
IETF network protocols ("network byte order".) Those versions of
EverParse introduce the integer type ``UINT8BE`` to read a 8-bit
bitfield as MSB-first.

Constants and Enumerations
--------------------------

3d provides a way to define numerical constants:

.. literalinclude:: ConstColor.3d
    :language: 3d

Alternatively, 3d provides a way to define enumerated types:

.. literalinclude:: Color.3d
    :language: 3d

The validator for ``coloredPoint`` will check that the value of
the field ``col`` is either 1, 2 (for ``green``), or 42.

Contrary to structs, enum types cannot be marked ``entrypoint``.

The first enum label must be associated with a value.

The support type (here ``UINT32``) must be the same type as the type
of the values associated to each label.

Due to a limitation in the way 3d currently checks for the absence of
double-fetches, values with enum type cannot be used in
constraints. For example, the following code is currently rejected.

.. code-block:: 3d
                
  UINT32 enum color {
    red = 1,
    green,
    blue = 42
  };

  typedef struct _enum_constraint {
    color col;
    UINT32 x
    {
       x == 0 || color == green
    };
  } _enum_constraint ;

With the following error message:

.. code-block:: text

   (Error) The type of this field does not have a reader, either because its values are too large or because reading it may incur a double fetch; subsequent fields cannot depend on it


One must instead write:

.. literalinclude:: EnumConstraint.3d
   :language: 3d

We expect to lift this limitation soon.


Parameterized data types
------------------------

3d also offers the possibility to parameterize a data type description
with arguments that can then be reused in constraints. For instance,
the following ``BoundedSum.3d`` data description defines a pair of two
integers whose sum is bounded by a bound provided by the user as
argument:

.. literalinclude:: BoundedSum.3d
    :language: 3d
    :start-after: SNIPPET_START: boundedSum
    :end-before: SNIPPET_END: boundedSum

Then, these arguments will show up as arguments of the
corresponding validator in the ``BoundedSumWrapper.h`` header produced
by 3d:

.. literalinclude:: BoundedSumWrapper.h
    :language: c
    :start-after: SNIPPET_START: BoundedSum
    :end-before: SNIPPET_END: BoundedSum

Parameterized data types can also be instantiated within the ``.3d``
file itself, including by the value of the field of a struct:

.. literalinclude:: BoundedSum.3d
    :language: 3d
    :start-after: SNIPPET_START: mySum
    :end-before: SNIPPET_END: mySum

A parameterized data type can also check whether a condition on its
arguments holds before even trying to check its contents:

.. literalinclude:: BoundedSumWhere.3d
    :language: 3d

In this case, the validator for ``boundedSum`` would check
that ``bound <= 1729``, before validating its fields.
   

Tagged unions or ``casetype``
------------------------------

3d supports *tagged unions*: a data type can store a value named *tag*
and a *payload* whose type depends on the tag value. The tag does not
need to be stored with the payload (e.g. it could be a parameter to the
type).

For instance, the following description defines the type of an integer
prefixed by its size in bits.

.. literalinclude:: TaggedUnion.3d
    :language: 3d
    :start-after: SNIPPET_START: casetype$
    :end-before: SNIPPET_END: casetype$

.. warning::

  3d does not enforce that all cases of a union be of the same size,
  and 3d does not introduce any implicit padding to enforce it. Nor
  does 3d introduce any alignment padding. This is in the spirit of
  keeping 3d specifications explicit: if you want padding, you need to
  add it explicitly. See also the section on :ref:`alignment <sec-alignment>`.

A ``casetype`` type actually defines an untagged union type dependent
on an argument value, which can be reused, e.g. for several types that
put different constraints on the value of the tag.

A ``casetype`` type can also be marked ``entrypoint``.

Rather than defining a top-level ``casetype``, one can define a type by cases as
a field in a struct. For example, the following type is equivalent to the one
before:


.. literalinclude:: TaggedUnion.3d
    :language: 3d
    :start-after: SNIPPET_START: switch literal$
    :end-before: SNIPPET_END: switch literal$


Arrays
------

A field in a struct or a casetype can be an array.

Arrays in 3d differ from arrays in C in a few important ways:

* Rather than counting elements, the size of an array in 3d is always
  given in bytes.

* Array sizes need not be a constant expression: any integer
  expression is permissible for an array, so long as it fits in
  ``UINT32``. This allows expressing variable-sized arrays.
  
3d supports several kinds of arrays.

Byte-sized arrays
.................

* ``T f[:byte-size n]``
  
The notation ``T f[:byte-size n]`` describes a field named ``f`` holding an
array of elements of type ``T`` whose cumulative size in bytes is ``n``.

When ``sizeof(T) = 1``, 3d supports the notation ``T f[n]``, i.e., for
byte arrays, since the byte size and element count coincide, you need
not qualify the size of the array with a ``:byte-size`` qualifier.

Singleton arrays of variable size
.................................

* ``T f[:byte-size-single-element-array n]``
  
In some cases, it is required to specify that a field contains a
single variable-sized element whose size in bytes is equal to a given
expression. The notation above introduces a field ``f`` that contains
a single element of type ``T`` occupying exactly ``n`` bytes.

A variation is:

* ``T f[:byte-size-single-element-array-at-most n]``

which describes a field ``f`` that contains a single element of type
``T`` occupying at most ``n`` bytes, followed by padding bytes to make
up to ``n`` bytes. This construct thus always consumes exactly ``n``
bytes.

We expect to add several other kinds of variable-length array-like
types in the uture.

Actions
-------

In addition to semantic constraints on types, 3d allows augmenting the
the fields of a struct or union with imperative actions, which allows
running certain user-chosen commands at specified points during
validation.

Let's start with a simple example. Suppose you want to validate that a
byte array contains a pair of integers, and then read them into a
couple of mutable locations of your choosing. Here's how:

.. literalinclude:: ReadPair.3d
    :language: 3d

The struct ``Pair`` takes two out-parameters, ``x`` and ``y``. Out
parameters are signified by the ``mutable`` keyword and have pointer
types---in this case ``UINT32*``. Each field in the struct is
augmented with an ``on-success`` action, where the action's body is a
runs a small program snippet, which writes the ``first`` field into
``x``; the ``second`` field into ``y``; and returns ``true`` in both
cases. Actions can also return ``false``, to signal that validation
should halt and signal failure.

Now, in greater detail:

Action basics
.............

An action is a program composed from a few elements:

* Atomic actions: Basic commands to read and write variables
  
* Variable bindings and sequential composition
  
* Conditionals

* External function calls

An action is evaluated with respect to a handler (e.g.,
``on-success``) associated with a given field. We refer to this field
as the "base field" of the action.

An action is invoked by EverParse immediately after validating the
base field of the action. The action of the ``on-success`` handler is
invoked in case the field is valid (if preseent), otherwise the
``on-error`` handler is invoked (if present).

The on-success handler can influence whether or not validation of the
other fields continues by returning a boolean---in case an on-success
action returns false, the validation of the type halts with an error.

The on-error handler also returns a boolean: in case it returns false,
the error code associated with the validator mentions that an
on-error handler failed; if it returns true, the error code is the
error code associated with the failed validation of the base field. In
both cases, validation halts with an error.


Atomic actions
^^^^^^^^^^^^^^

* Expression ``e`` consist of variables and constants.

* ``*i = e``: Assigns the value of the expressions ``e`` to the memory referenced by the pointer ``i``.
  
* ``*i``: Dereferences the pointer ``i``

* ``field_pos``: Returns the offset of base field of the action from
  the base of the validation buffer as a ``UINT32`` value.

* ``field_ptr``: Returns a pointer to base field of the action as a
  ``PUINT8``, i.e., an abstract pointer to a ``UINT8``.

* ``return e`` Returns a boolean value ``e``

* ``abort``: Causes the current validation process to fail.

Composing atomic actions sequentially and conditionally
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Composite actions can be built in a few ways:

* Atomic actions: For any atomic action ``a``, ``a;`` (with a trailing
  semicolon) is a composite action ``p``.

* Sequential composition: ```a; p`` Given an atomic action ``a``, and
  a compositite action ``p``, the form ``a;p`` runs ``a`` then ``p``.

* Variable binding: ``var x = a; p`` Given an atomic action ``a``,
  and a compositite action ``p``, the form ``var x = a; p`` runs ``a``,
  stores its result in the new variable ``x`` (local to the
  action), and then runs ``p`` (where ``p`` may mention `x`

* Conditionals: ``if (e) { p }`` is a conditional action that runs the
  composite actions ``p`` only if the condition ``e`` is
  true. Additionally, ``if (e) { p0 } else { p1 }`` is also legal,
  with the expected semantics, i.e., ``p1` is run in case ``e`` is
  false.

* External function calls: an action can call a user-defined callback
  C function. The user first needs to declare the callback function with
  a top-level declaration in the 3D file: for instance,
  ``extern UINT8 myFunction(UINT32 myArg1, UINT16 myArg2)``
  Then the user can call this function in an action, with
  ``var myReturnValue = myFunction(e1, e2);``
  The user can also declare a function that returns no value, with
  ``void`` as its return type. Then, the user can call this function
  directly as a statement in an action, without ``var`` :
  ``myFunction(e1, e2);``
  An external function can also accept out-parameters, using
  ``mutable myType* myArg`` in its 3D declaration.


Another example
^^^^^^^^^^^^^^^

Consider the following definition:

.. literalinclude:: GetFieldPtr.3d
    :language: 3d
    :start-after: SNIPPET_START: GetFieldPtr.T
    :end-before: SNIPPET_END: GetFieldPtr.T

Here, we define a type ``T`` with an out-parameter ``PUINT8* out``,
i.e., pointer to a pointer to a ``UINT8``.

Associated with field ``f2`` we have an on-success handler, where we
read a pointer to the field ``f2`` into the local variable ``x``;
then, we write ``x`` into ``*out``; and finally return ``true``.

.. note:: The return type of ``field_ptr`` is ``PUINT8``. In
   EverParse, a ``PUINT8`` is a pointer into the input buffer, unlike
   a ``UINT8*`` which may point to any other memory. This distinction
   between pointers into the input buffer and other pointers allows
   EverParse to prove that validators never read the contents of the
   input buffer more than once, i.e., there are no double fetches from
   the input buffer. As such, the ``out`` parameter should have type
   ``PUINT8*`` rather than ``UINT8*``.

Actions that always succeed
^^^^^^^^^^^^^^^^^^^^^^^^^^^

For actions that always succeed, 3d supports a more concise notation, using the
``:act`` form, as shown below:

.. literalinclude:: GetFieldPtr.3d
    :language: 3d
    :start-after: SNIPPET_START: GetFieldPtr.T act$
    :end-before: SNIPPET_END: GetFieldPtr.T act$

This is equivalent to the prior ``:on-success`` action shown earlier.


Restrictions
............

* Actions can only be associated with fields.

* Actions cannot be associated with the elements of an array, unless
  the array elements themselves are defined types, in which case they
  can be associated with the fields of that type, if any.

* Actions cannot be associated with bit fields.

.. _sec-alignment:

Alignment
---------

As mentioned previously, 3d does not introduce any implicit alignment padding.
However, it is often convenient to use 3d to model the in-memory layout of a C
structure, including the alignment padding that a C compiler would insert.
Rather than requiring the user to manually insert padding fields, 3d allows
decorating a struct with an ``aligned`` attribute, which instructs the 3d
frontend to add padding between fields modeling the behavior of a C compiler.
This page provides a useful reference about `alignment padding in C
<https://learn.microsoft.com/en-us/cpp/c-language/alignment-c?view=msvc-170>`_.

For example, consider the following structs:

.. literalinclude:: Align.3d
  :language: 3d
  :start-after: SNIPPET_START: structs
  :end-before: SNIPPET_END: structs


The ``aligned`` attribute to each struct adds alignment padding
between fields.

  * Both fields of the type ``point`` are aligned at 2-byte boundaries; so no
    padding is inserted between them.

  * In type ``coloredPoint1`` the field ``color`` is aligned at a 1-byte boundary,
    while ``pr`` is aligned at a 2-byte boundary; so 1 byte of padding is inserted
    between them. So, the whole struct consumes six bytes, aligned at a 2-byte
    boundary.

  * In type ``coloredPoint2`` the field ``pt`` is aligned at a 2-byte boundary, but
    the type ``color`` is aligned at a 1-byte boundary. So, no padding is inserted
    between them. But, the resulting type must be aligned at a 2-byte boundary,
    so 1 byte of padding is inserted after the ``color`` field---so, the whole
    struct consumes six bytes.

The 3d compiler emits diagnostics describing the padding it inserts::

  Adding padding field in Align._coloredPoint1 for 1 bytes at (preceding field Align.point pt;)
  Adding padding field in Align._coloredPoint2 for 1 bytes at (end padding)

The ``aligned`` attribute can also be adding to casetypes, though the behavior is
more limited:

.. literalinclude:: Align.3d
  :language: 3d
  :start-after: SNIPPET_START: union
  :end-before: SNIPPET_END: union

Here, we have an aligned "union". 3d checks that every branch of the union
describes field with the same size. It *does not* insert padding to make every
type have the same size. For example, if the ``UINT16 other`` fields were left out
of the default case of ``Value``, the 3d compiler would emit the following error
message::

  With the 'aligned' qualifier, all cases of a union with a fixed size must have the same size; union padding is not yet supported

Note, the ``aligned`` attribute is not allowed on typedefs, enums, or other kinds
of 3d declarations.

Variable-length Types
......................

The ``aligned`` attribute is also supported on variable-length types, but use it
with care. 3d inserts alignment padding to mimic the behavior of a C compiler;
but C does not support variable-length types! There are many idioms that C
programmers use to model variable-length types, e.g., a zero-length array at the
end of a struct; sometimes a 1-length array; and sometimes and array with no
length at all, using `C99 flexible array members
<https://www.gnu.org/software/c-intro-and-ref/manual/html_node/Flexible-Array-Fields.html>`_

A rule of thumb for ``aligned`` on variable-length types is that it only applies
to the fixed-size prefix of the type. For example, consider the following type:

.. literalinclude:: Align.3d
  :language: 3d
  :start-after: SNIPPET_START: TLV
  :end-before: SNIPPET_END: TLV

The output from the 3d compiler includes the following diagnostic::

  Adding padding field in Align._tlv for 3 bytes at (preceding field dependent UINT32 length;)
  Adding padding field in Align._tlv for 1 bytes at (preceding field Align.Value(tag) payload[:byte-size length];)

* 3d adds 3 bytes after ``tag`` and preceding ``length``, since ``length`` is 4-byte
  aligned.

* It adds 1 byte after ``other`` and preceding the ``payload`` field, since the
  payload is a ``Value`` array and is 2-byte aligned.

* But, notice, it does not add a padding field after ``payload`` to align the
  ``other2`` field, since ``other2`` follows a variable-length field.

In contrast, consider the following type in C:

.. code-block:: c

  typedef struct _tlv {
    UINT8 tag;
    UINT32 length;
    UINT8 other;
    Value payload[0];
  } TLV;

The alignment of the ``Value payload[0]`` field is 2, but its size is zero. So,
a C compiler adds the following padding:

* 3 bytes after ``tag`` and preceding ``length``, since ``length`` is 4-byte
  aligned.

* 1 byte after ``other`` and preceding the ``payload`` field, since the payload
  is 2-byte aligned.

* 2 bytes of end padding, since the alignment of ``TLV`` is 4

In such cases, if one really intends to model a variable-length C type, it is
better to explicitly insert alignment padding to match a given layout, rather
than relying on 3d to insert alignment padding that may not match the layout you
have in mind.

.. literalinclude:: Align.3d
  :language: 3d
  :start-after: SNIPPET_START: TLV_ALT
  :end-before: SNIPPET_END: TLV_ALT

Static Assertions to Validate Alignment
........................................

To confirm that the alignment 3d inserts matches the layout of a C type, 3d
automatically generates C types corresponding to every type with an ``aligned``
attribute, and emits C static assertions to check that the sizes and field
offsets computed by 3d match what the C compiler computes.

For example, for the types defined in this section, 3d generates a file
``AlignAutoStaticAssertions.c`` with the contents below:

.. literalinclude:: out/AlignAutoStaticAssertions.c
  :language: c

Notice that in the C transcription of the type ``TLV``, 3d simply omits the
suffix of the type starting with the variable-length payload field.

If you compile this file with a C compiler (e.g., ``gcc -c
AlignAutoStaticAssertions.c``), you will see that the following static assertion
will fail, an indicator that for this variable-length type, you will be better
off removing the ``align`` attribute and explicitly modeling the alignment
padding yourself:

.. code-block:: c

  EVERPARSE_STATIC_ASSERT(sizeof(TLV) == 10);

This is becase the C compiler inserts 3 bytes of end padding after the field
``other``, whereas with the variable-length field, 3d adds 1 byte of padding.

.. note:: 

  Arguably, due to these potential discrepancies, 3d could simply forbid the
  ``aligned`` attribute on variable-length types.


Explicitly checking 3d types for correspondence with existing C types
----------------------------------------------------------------------

In addition to automatically generating static assertions for types with the
``aligned`` attribute, 3d allows one to explicitly assert the correspondence
between some 3d typed and C types.

A typical scenario is that you have an existing C program with some collection
of types defined in a file ``Types.h``.  You've written a ``Types.3d`` file to
defined validators for byte buffers containing those types, typically *refining*
the C types with additional semantic constraints and also with actions. Now, you
may want to make sure that types you defined in ``Types.3d`` correspond to the
types in ``Types.h``, e.g., to ensure that you didn't forget to include a field
in a struct, or that you've made explicit in your ``Types.3d`` the alignment
padding between struct fields that a C compiler is sometimes requires to insert.

To assist with this, 3d provides the following feature:

.. literalinclude:: GetFieldPtr.3d
  :language: 3d

Following the type definitions, the ``refining`` section states that
the type ``S`` defined in the C header file ``GetFieldPtrBase.h`` is
refined by the type ``T`` defined here. As a result of this
declaration, 3d emits a static assertion in the C code of the form

.. code-block:: c

  #include "GetFieldPtrBase.h"
  C_ASSERT(sizeof(S) == 30);
   
checking that the ``sizeof(S)`` as computed by the C compiler matches
3d's computation of the ``sizeof(T)``.

In generality, the refining declaration takes the following form:

.. code-block:: 3d

  refining "I1.h", ..., "In.h" {
      S1 as T1, ...
      Sm as Tm
  }


where each ``Si`` is a type defined in one of the C header files
"I1.h", ..., "In.h", and the ``Ti`` are types defined in the current
3d file. In case the types have the same names, one can simply write
``T`` instead of ``T as T``.

As a second example, let's revisit the type from the :ref:`alignment section
<sec-alignment>`, aiming to show that the 3d type corresponds to the C types
defined in the header file `AlignBase.h` shown below:

.. literalinclude:: AlignBase.h
  :language: c

Let's also decorate the 3d file with the following refining declaration:

.. literalinclude:: Align.3d
  :language: 3d
  :start-after: SNIPPET_START: refining
  :end-before: SNIPPET_END: refining
  
The 3d compiler emits the following static assertions:

.. literalinclude:: out/AlignStaticAssertions.c
  :language: c

As before, the ``sizeof(TLV)==10`` fails, because of differences in alignment
padding with variable-length structures, a good indication to use explicit 
alignment padding for variable-length types.

Generating code with for several compile-time configurations
------------------------------------------------------------

Sometimes one wants to write a single format specification to
accommodate several compile-time configurations, e.g., to support
multiple architectures. 3D offers some limited support for decorating
a specification with compile-time conditionals familiar to C
programmers, e.g., ``#if`` and ``#else``, and to generate C code
while preserving these C preprocessor directives.

For example, the listing below shows an integer type that can either
be represented using 64 bits (if ``ARCH64`` is true) or 32 bits.

.. literalinclude:: PointArch_32_64.3d
    :language: 3d

To compile such a file using 3D, we also need to provide a
``.3d.config`` file that declares all the compile-time flags used in
the specification and mentions a C header file in which to find
definitions for those flags. Here is a sample config file:

.. literalinclude:: Arch.3d.config

Then, one can invoke ``3d.exe --config Arch.3d.config
PointArch_32_64.3d --batch``, which produces the following C code as
output.

In the header file ``PointArch_32_64.h``, we see an include for
the header file mentioned in the config:

.. code-block:: c

   #include "arch_flags.h"

In the generated C file, ``PointArch_32_64.c``, we see the code below,
with the suitable preprocessor directives protecting the two variants
of the the ``Int`` type declared in the source 3d file.

.. code-block:: c

   static inline uint64_t
   ValidateInt(...) {
   {
      #if ARCH64
      /* Validating field x */
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      ...
      #else
      /* Validating field x */
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      ...
      #endif
   }


Validating Data with Indirections or Pointers
---------------------------------------------

In some cases, rather than parsing from a flat array of contiguous memory, one
wants to parse a structure with indirections, i.e., the input buffer may contain
pointers to other chunks of memory containing sub-structures to be parsed.

Parsing such pointer-rich structures is delicate, since before following a
pointer, one needs to check that the pointer references valid memory. Given a
raw pointer (just a memory address), one cannot, in general, check that the
pointer is valid. However, in some scenarios, such checks are possible, e.g., in
kernel code, it may be possible to probe a pointer to check that it is valid,
and only then proceed to read from it. 3d supports parsing structures containing
pointers, provided safe probing functions can be provided by the caller.

Pointer Types
.............

Let's start by looking at some basic support for pointer types in 3d.

As in C, any field of a structure can be marked as a pointer: here, below, the
second field ``y`` is marked as pointer to a ``UINT32``.

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: simple pointer1$
  :end-before: SNIPPET_END: simple pointer1$

By default, a pointer type is simply treated as an unsigned 64-bit integer and
3d will not dereference the pointer when validating a type. One can mark any
field as a pointer, not just fields with base type, and a pointer field can be
associated with a constraint, as any other field of a base type. The example
below shows a constraint on a pointer field checking that it is
non-null---notice that in the constraint,  the ``ptr`` value is just treated as
having type ``UINT64``. 

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: simple pointer2$
  :end-before: SNIPPET_END: simple pointer2$

One can also associate an action with a pointer field, e.g., reading its value
into an out parameter.

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: simple pointer3$
  :end-before: SNIPPET_END: simple pointer3$

One can also explicitly mark the size of a pointer, giving it the type
``UINT64`` (the default) or ``UINT32``, as shown in the examples below.

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: simple pointer4$
  :end-before: SNIPPET_END: simple pointer4$

Note, in all these examples, the *type* of pointed-to data is irrelevant: 3d
simply treats the pointer as an integer value.

Probing Pointers: A first example
.................................

We now look at how to traverse pointers, dereferencing them and validating the
data they point to.

Let's start with a simple example. Our goal is to validate a format that
contains a single indirection: a structure ``S`` containing a pointer to a
structure ``T``.

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: simple probe$
  :end-before: SNIPPET_END: simple probe$

The first line declares a ``probe`` function called ``ProbeAndCopy``. This is a
requirement on the user of the generated parser to link the generated code with
a function called ``ProbeAndCopy``. In fact, the generated code contains an
extern declaration with the signature shown below (in ``Probe_ExternalAPI.h``):

.. code-block:: c

  extern BOOLEAN ProbeAndCopy(
    uint64_t size,  //The number of bytes to copy
    uint64_t read_offset, //starting at this offset from the src pointer
    uint64_t write_offset, //writing to this offset in the dst buffer
    uint64_t src, //the source address to be probed and checked for validity
    EVERPARSE_COPY_BUFFER_T dst //the target buffer into which the data is to be copied
  );

That is, the ``ProbeAndCopy`` function is expected to check probe the source address, 
check its validity at ``read_offset``, and copy ``size`` bytes into the ``dst``
buffer starting at ``write_offset``.

Note, although a typical implementation may choose to copy memory into the
destination buffer, this not strictly required. In particular, the type
``EVERPARSE_COPY_BUFFER_T`` is also left to the user to define. In particular,
in ``EverParseEndianness.h``, we have

.. code-block:: c

  typedef void* EVERPARSE_COPY_BUFFER_T;

While in ``EverParse.h``, we further have:

.. code-block:: c

  extern uint8_t *EverParseStreamOf(EVERPARSE_COPY_BUFFER_T buf);

  extern uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T buf);

That is, the client code can choose any definition for
``EVERPARSE_COPY_BUFFER_T`` (since it is just a ``void*``), so long as it can
also provide two functions: ``EverParseStreamOf`` to extract a buffer of bytes
from a ``EVERPARSE_COPY_BUFFER_T``; and ``EverParseStreamLen`` to extract the
length of the buffer.

The second line defines another extern callback for ``extern probe (INIT)
ProbeInit``. This results in the following extern C declaration in
``Probe_ExternalAPI.h``:

.. code-block:: c

  extern BOOLEAN ProbeInit(
    uint64_t size,
    EVERPARSE_COPY_BUFFER_T dst
  )

The ``ProbeInit`` callback allows a caller to initialize the destination buffer,
preparing it to contain up to ``size`` bytes of data, e.g., if need be, one
could use this callback to allocate memory.

Let's return to the example to see how the ``ProbeAndCopy`` function is used.

The type ``T`` is just a struct with two fields, constrained by a lower bound.
The type ``S`` is more interesting. It starts with a ``UINT8 bound`` and then
contains a *pointer* ``t`` to a ``T`(bound)`` struct. To emphasize the point,
the following picture illustrates the layout::

     bytes
     0........1........2........3........4........5........6........7........8........9 
 S:  { bound  |              tpointer                                                 }
                                |
                                |
      .-------------------------.                            
      |
      v 
     0........1........2........3........4........5........6........7........8.........9 
 T:  {        x        |        y        }

  
The input buffer represents the ``S`` structure in 5 bytes, beginning with one
byte for the ``bound``, and following by 8 bytes for the ``tpointer``
field---currently, 3D treats pointer fields as always 8 bytes long.

The ``tpointer`` field contains a memory address that points to the a ``T``
structure, which is represented in 4 bytes, with 2 bytes each for its ``x`` and
``y`` fields, as usual.

The 3D notation below:

.. code-block:: 3d

  T(bound) *tpointer probe ProbeAndCopy(length = sizeof(T), destination = dest);

Instructs the parser to:

  * First, read the contents of the ``tpointer`` field into a local vairable ``src``

  * Then, call ``ProbeInit(4, dest)`` to prepare the destination buffer, where
    ``sizeof(T)=4``.

  * Then, if ``ProbeInit`` succeeds, use ``ProbeAndCopy(sizeof(T), 0, 0, src,
    destS)`` check that the ``sizeof(T)`` bytes starting at the address pointed
    to by ``tpointer`` is valid memory, using the ``dest`` parameter as its copy
    buffer.

  * Finally, if ``ProbeAndCopy`` succeeds, then validate that
    ``EverParseStreamOf(dest)`` buffer contains a valid ``T(bound)`` structure,
    in ``EverParseStreamLen(dest)`` bytes.

Ultimately, the generated code provides the following signature for a C caller,
in ``ProbeWrapper.h``, to validate a buffer pointers to by ``base``, containing
at least ``len`` bytes, checking that it contains a valid ``S(dest)``.

.. code-block:: c

  BOOLEAN ProbeCheckS(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len);


Probing Multiple Indirections
.............................

Continuing our simple example, let's add another layer of indirection:, with a
structure ``U`` containing a pointer to ``S``. This can be specified as shown
below:

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: multi probe$
  :end-before: SNIPPET_END: multi probe$


* The type ``U`` packages a pointer to an ``S`` structure with a tag.

* The specification of ``U`` is parameterized by `two` destintation buffers:
  ``destS`` to receive the contents of the memory referenced by ``spointer``;
  and ``destT`` to receive the contents of the memory referenced by
  ``tpointer``.

Operationally, the validator for ``U`` proceeds by:

* First, validating the tag field (in this case, it is a noop)

* Then, reading ``spointer`` into ``srcS`` and

  - Calling ``ProbeInit(sizeof(S), destS)``

  - Then, ``ProbeAndCopy(sizeof(S), 0, 0, srcS, destS)``

  - Then, validate ``EverParseStreamOf(destS)`` contains a valid ``S(destT)``.

The validation of ``S(destT)`` proceeds as described before, copying the
contents of ``tpointer`` into ``destT`` and validating it.

The C interface includes the following:

.. code-block:: c

  BOOLEAN ProbeCheckU(EVERPARSE_COPY_BUFFER_T destS, EVERPARSE_COPY_BUFFER_T destT, uint8_t *base, uint32_t len);

Note, one can also reuse the same copy buffer for multiple probe, so long as the
probes are done sequentially. For instance, we use several probes below, reusing
``destT`` multiple times to parser the nested ``T`` structure within ``sptr``,
and again for ``tptr`` and ``t2ptr``.

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: reuse copy buffer$
  :end-before: SNIPPET_END: reuse copy buffer$

This is allowed since the probes are done sequentially, and the copy buffer is
not reused before the probe \& validation are complete. On the other hand, if
one were to try to reuse a copy buffer before its probe \& validation are
complete (e.g., by using ``destT`` as the destination buffer for ``sptr``) 3D
issues an error message::

  ./Probe.3d:(30,16): (Error) Nested mutation of the copy buffer [destT]

Top-level Probes
................

Rather than attaching a probe to a field, one can also attach a probe to an
entire type. For instance, one can write the following:

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: indirect$
  :end-before: SNIPPET_END: indirect$


This type specifies the following layout, with an input buffer containing a
single pointer which refers to a buffer containing a valid struct with three
fields.::



     bytes
     0........1........2........3........4........5........6........7........8
   I:{                        pointer                                        }
                                |
                                |
      .-------------------------.                            
      |
      v 
     0........1........2........3........4........5........6........7........8.........9 
  TT:{        x                          |                 y                 |   tag    }

This yields the following C interface, with two entry points. The first is to
probe and validate a pointer to the type ``Indirect``, while the second is to
validate a ``struct Indirect``.

.. code-block:: c

  BOOLEAN ProbeProbeAndCopyCheckIndirect(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr);
  BOOLEAN ProbeCheckIndirect(uint8_t *base, uint32_t len);

The specification is equivalent to the following, though more concise:

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: indirect alt$
  :end-before: SNIPPET_END: indirect alt$

.. _Coercing_pointers:

Coercing Pointer Types
......................

One can also add a probe to a pointer with an explicit pointer size, so long as
one also provides a callback to convert a value from that explicit pointer size
to ``UINT64``, as in the example below:

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: coerce$
  :end-before: SNIPPET_END: coerce$

Here, we first define a callback ``UlongToPtr`` to convert a ``UINT32`` to a
``UINT64``. 

In ``Probe_ExternalAPI.h``, this extern declaration produces the following C
signature:

.. code-block:: c
    
    extern uint64_t UlongToPtr(uint32_t ptr);

Then, in ``CoercePtr``, we can qualify our pointer type to 32-bits: the 3d
compiler will automatically insert the ``UlongToPtr`` coercion on the 32-bit
pointer value before called ``ProbeAndCopy`` with the coerced pointer value.

.. note::

  If you declare more than one coercion to coerce between a pair of types, 3d
  will likely complain with the following error:

  .. code-block:: text

    ./Probe.3d:(132,33): (Error) Multiple extern coercions found for UINT32 -> UINT64: Probe.UlongToPtr, Probe.UlongToPtr2

  This is because 3d applies coercions implicitly, and if multiple coercions are
  found between a pair of types, it cannot choose which coercion to apply.


Multiple Probe Callbacks
........................

Sometimes, it can be useful to have several probe callbacks, e.g., some of them
may copy, while for others it might be safe to validate the data in place.

The example below shows how to use multiple probes:

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: probe_and_copy_alt$
  :end-before: SNIPPET_END: probe_and_copy_alt$

* The extern declaration of ``ProbeAndCopyAlt`` produces a second extern
  declaration in ``Probe_ExternalAPI.h`` for the client code to provide and link
  with.

* One can associate multiple entrypoint probe attributes on a type, each with a
  different probe and copy function.

* One can also associate different probes on each field of a type.

The resulting C interface contains multiple entry points, one for each variant
of probing entry point, and one for the non-probing variant:

.. code-block:: c

  BOOLEAN ProbeProbeAndCopyCheckMultiProbe(
    EVERPARSE_COPY_BUFFER_T destT1,
    EVERPARSE_COPY_BUFFER_T destT2,
    EVERPARSE_COPY_BUFFER_T probeDest,
    uint64_t probeAddr);

  BOOLEAN ProbeProbeAndCopyAltCheckMultiProbe(
    EVERPARSE_COPY_BUFFER_T destT1,
    EVERPARSE_COPY_BUFFER_T destT2,
    EVERPARSE_COPY_BUFFER_T probeDest,
    uint64_t probeAddr);

  BOOLEAN ProbeCheckMultiProbe(
    EVERPARSE_COPY_BUFFER_T destT1,
    EVERPARSE_COPY_BUFFER_T destT2,
    uint8_t *base,
    uint32_t len);


.. note:: 

  External declarations for probe callbacks and for pointer coercions are in
  scope for the entire file, since 3d can call these functions implicitly when
  elaborating a specification. So, unless you are an expert and have a
  particular need for multiple probe callbacks, it is possible that declaring
  multiple probe callbacks can result in errors such as the one below,
  especially when using multiple probe callbacks in conjuction with
  :ref:`specialization <Specialization>`.
  
  .. code-block:: text

     ./Specialize1.3d:(10,30): (Error) Found multiple probe functions: Specialize1.ProbeAndCopyAlt, Specialize1.ProbeAndCopy


Nullable Pointers
.................

By default, all probed pointer fields are expected to be non-null. If a pointer
value happens to be null, then either

* The ``ProbeAndCopy`` function can return false, in which case validation fails

* Or, the ``ProbeAndCopy`` function can return true, in which the generated code
  would proceed to try to validate the contents of the destination buffer, which
  will likely fail.

If a pointer in a data structure is allowed to be null, then one can mark it as
such with a nullable qualifier, ``pointer?`` as shown below.

.. literalinclude:: Probe.3d
  :language: 3d
  :start-after: SNIPPET_START: nullable$
  :end-before: SNIPPET_END: nullable$

For a pointer with a nullable qualifier, the generated code first checks if the
pointer is non-null:

* If the pointer is null, validation succeeds without calling the probe function

* If the pointer is non-null, the probe function is called, and validation
  proceeds as in the non-null case.


An End-to-end Executable Example
................................

A small but fully worked out example `is available in the EverParse repository
<https://github.com/project-everest/everparse/tree/master/src/3d/tests/probe>`_.

It shows the use of multiple probe functions, linked with callbacks implemented
in C, as well as a main C driver program that validates several example inputs
containing pointers.

.. _Specialization:

Specialization for Different Pointer Sizes
------------------------------------------

Consider writing a specification to handle messages that could be sent from both
32- and 64-bit machines, particularly if those messages contain pointers. This
scenario happens in practice, e.g., when a 64-bit OS kernel shares memory with
user-mode processes that may be either native 64-bit processes or emulated
32-bit processes.

3d supports a form of compile-time specialization that allows one to write a
specification with 64-bit clients in mind, and then have the compiler specialize
the 64-bit specification also for use with a 32-bit clients. There are many
subtle elements to consider, and we describe them gradually, starting with a
simple first example.


A First Example
...............

As in the previous section, we have a format with two levels of indirection:
``R64`` with a pointer to ``S64``, and ``S64`` with a pointer to ``T``.

.. literalinclude:: Specialize1.3d
  :language: 3d
  :start-after: SNIPPET_START: prefix$
  :end-before: SNIPPET_END: prefix$

A First Manual Attempt
^^^^^^^^^^^^^^^^^^^^^^^

If we wanted to specify a variant of ``R32`` with a 32-bit pointer to a ``S32``
which in turn had a 32-bit pointer to a ``T``, we could explicitly rewrite our
entire specification, as shown below.

.. literalinclude:: Specialize1.3d
  :language: 3d
  :start-after: SNIPPET_START: attempt0$
  :end-before: SNIPPET_END: attempt0$

At the top-level of the specification, one could then define ``RMux``, a
multiplexing layer, which depending on the value of ``requestor32``, validates
either an ``R32_Attempt`` or an ``R64``.

This looks plausible, even though it is verbose and leads to a lot of
duplication. However, even aside from the verbosity this revised specification
has a deeper problem.

Consider the case where ``requestor32=true``: if the probe on ``ptrS`` runs
successfully, it will have copied ``sizeof(S32Attempt)=12`` bytes, and then
checked that the bytes copied into ``destS`` is a valid ``S32Attempt``. If after
this validation, a caller wants to, say, read the value of the ``s2`` field,
then they would need to read ``4`` bytes at offset ``8`` from ``destS`` buffer. 

On the other hand, when ``requestor32=false``: if the probe on ``ptrS`` runs
successfully, it will have copied ``sizeof(S64)=24`` bytes (including the 4
bytes of padding between ``s1`` and ``ptrT`` and then 4 bytes of padding after
the field ``s2``), and then checked that the bytes copied into ``destS`` is a
valid ``S64``. If after this validation, a caller wants to read the value of the
``s2`` field, then they would need to read ``4`` bytes at offset ``16`` from
``destS`` buffer. 

That is, even after reading and validating the input, the caller has to
distinguish the cases of ``requestor32``. We would prefer instead to have a way
to handle either 32- or 64-bit inputs, but after validation, we would like the
contents of the destination buffers to always be in 64-bit form, for easy
manipulation by native 64-bit kernel code, without needing to bifurcate further
handling of 32- and 64-bit inputs.

A Second Manual Attempt
^^^^^^^^^^^^^^^^^^^^^^^

Here's another attempt at specializing ``R64``:

.. literalinclude:: Specialize1.3d
  :language: 3d
  :start-after: SNIPPET_START: manual$
  :end-before: SNIPPET_END: manual$

This time, we have an even more verbose specification, but we'll see that it
actually achieves what we want. This specification is legal 3d, and it uses an
explicit, low-level form of probing functions that we do not typically expect
users to write. But, it's a useful intermediate language to explain things.

The first field, ``r1``, is as before.

The second field is an explicitly qualified pointer, qualified to
``pointer(UINT32)`` and with probe block associated with it. Our goal is to
coerce probe the input pointer ``ptrS`` and read its contents while coercing it
into a 64-bit layout, and then to validate that the copied bytes is a valid
``S64(r1, destT)``.

The probe block will first call ``ProbeInit``, initializing the ``destS``
buffer, preparing it to receive ``sizeof(S64)`` bytes. Then, within the probe
block, it executes a sequence of actions:

* Copy the first 4 bytes references by ``ptrS``--this is the ``s1`` field

* Skip 4 bytes of alignment padding

* Then read a 32 bit pointer ``ptrT``, coerce it to 64-butes, and write it into
  the destination buffer

* Then copy the next 4 bytes from the input buffer (field ``s2``)

* Finally, skip 4 bytes of padding at the end

After the probe block executed, we validate the ``EverParseStreamOf(destS)`` to
contain a valid  ``S64(r1, destT)``, which in turn will probe ``ptrT`` etc.

This does what we want, in the sense that if validation succeeds, then ``destS``
contains a 64-bit representation of the input, regardless of ``requestor32``,
and the caller can then proceed uniformly, without needing to bifurcate its
handling of 32- and 64-bit clients.

However, writing low-level coercions like this is impractical and error prone.

Automated Specialization
^^^^^^^^^^^^^^^^^^^^^^^^

Instead, 3d offers a ``specialize`` directive, to automatically rewrite a tree
of definitions rooted at a given type, replacing each occurrence of an
*unqualified* pointer type with an ``pointer(UINT32)``.

.. literalinclude:: Specialize1.3d
  :language: 3d
  :start-after: SNIPPET_START: specialize$
  :end-before: SNIPPET_END: specialize$

This instructs 3d to automatically generate the definition for ``R32`` from
``R64``, in the style of ``R32Manual``. In doing so, 3d will also try to
specialize the probe function on the nested ``ptrT`` in the ``S64``, but in
doing so it will discover that there is nothing to specialize in ``T`` and the
behavior of probing ``ptrT`` will be unchanged.

In order to use the specialize directive, we need to define a few additional
callbacks. 

.. literalinclude:: Specialize1.3d
  :language: 3d
  :start-after: SNIPPET_START: specialize$
  :end-before: SNIPPET_END: specialize$

The first callback, a ``UlongToPtr`` coercions, we saw :ref:`before
<Coercing_pointers>`: we'll need it to coerce a 32-bit pointer to 64-bits. It
produces the following C signature:

.. code-block:: c

  extern uint64_t UlongToPtr(uint32_t ptr);

The next callback, ``ProbeAndReadU32`` produces the following C signature:

.. code-block:: c

  extern uint32_t ProbeAndReadU32(
    BOOLEAN *failed,
    uint64_t read_offset,
    uint64_t src,
    EVERPARSE_COPY_BUFFER_T dest);

It probes a pointer ``src`` at a given ``read_offset``, checks its validity, and
reads 4 bytes from that offset and returns it as a ``uint32_t``. If the validity
check fails, it must set its out parameter ``failed`` to true. It typically does
not use its last parameter ``dest``, though this can be used by the caller to
provide useful contextual information.

Finally, the  callback ``WriteU64`` produces the following C signature:

.. code-block:: c

  extern BOOLEAN WriteU64(
    uint64_t value,
    uint64_t write_offset, 
    EVERPARSE_COPY_BUFFER_T destination);

It allows writing a single ``uint64_t`` ``value`` at a given ``write_offset``
into a destination buffer ``EVERPARSE_COPY_BUFFER_T``. If the write fails, e.g.,
because ``write_offset`` is out of bounds, then it must return ``false``,
otherwise ``true``.


With ``R32`` now automatically defined, we can easily define our multiplexing
layer, as shown below.

.. literalinclude:: Specialize1.3d
  :language: 3d
  :start-after: SNIPPET_START: multiplex$
  :end-before: SNIPPET_END: multiplex$

First Example in its Entirety
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We've gone through several iterations to arrive at our first example of
specialization. Here is the final specification in its entirety:



.. literalinclude:: Specialize1Standalone.3d
  :language: 3d


What is Proven About Specialization
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Safety**

As with all code produced by 3d, we prove that the generated code is:

* memory safe
* arithmetically safe
* has no undefined behaviors
* is double-fetch free

For specifications with probes, these guarantees are, of course, conditional on
the behavior of the extern callbacks. In particular, the callbacks implemnted in
C must themselves be memory safe, e.g., ``ProbeAndCopy(n, rd, wr, src, dest)``
must safely check that ``src + rd`` points to ``n`` bytes of valid memory and
that safely copies those ``n`` bytes into ``dest`` at offset ``wr`` is safe.

**Soundness**

We also prove that if validation succeeds, then the destination buffers contain
valid representations of their specified types. For instance, in the example
above, we prove that ``destS`` contains a valid representation of an ``S64(r1,
destT)`` and that ``destT`` contains a valid representation of ``T(s1)``.

**Completeness**

For non-specialized specifications, we usually prove a completeness property,
namely that if the input contains a well-formatted representation of a type
``T``, then the generated validator is guaranteed to accept that input.

Our proof for specialization does not cover this property: in particular,
formally, we have not yet proven that a well-formatted 32-bit input will always
be correctly coerced to a 64-bit layout and then accepted by the validator.

More concretely, an ideal result would be that an input correctly formatted
according to ``R32Attempt`` will always be accepted by the type ``R32`` computed
as a specialization of ``R64``. However, this equivalence is not yet covered by
our proofs.

We are working to enrich our proofs to cover this property.

**Static assertions**

Computing coercions between different layouts of types based on
architecture-specific details of compilers is delicate. Rather than trusting
outright 3d's implementation of the layout of structures including alignment
padding for 32- and 64-bit layouts, 3d emits static assertions to check that the
layout it computes corresponds to the layout for the corresponding structures
computed by whatever C compiler one uses to compile the code.

For our example above, 3d automatically generates a ``refining`` block and emits
the following C code:

.. literalinclude:: out/Specialize1StandaloneAutoStaticAssertions.c
  :language: c



An End-to-end Executable Example
................................

A small but fully worked out example `of specialization is available in the
EverParse repository
<https://github.com/project-everest/everparse/tree/master/src/3d/tests/specialize_test>`_.

It shows an example similar to the one developed above, but linked with a main C
program and test driver. It also illustrates the use of nullable pointers in
conjunct with probing and specialization.

Limitations on Variable-length Structures
.........................................

Automated specialization has only limited support for variable-length
structures. The main restriction is that a coercion between types cannot depend
on the data being coerced. We illustrate with a couple of examples:

Consider the following canonical tag-length-value encoding:


.. code-block:: 3d

  typedef struct _UNION(UINT8 tag) {
      switch (tag) {
          case 0:
              UINT8 case0;
          case 1:
              UINT16 case1;
          default: 
              UINT32 other;
      } field;
  } UNION;

  typedef struct _TLV
  {
      UINT8 tag;
      UINT32 length;
      UNION(tag) payload[:byte-size length];
  } TLV;


Now, let's say one wanted to prove a pointer to a ``TLV``, one could attempt
this:

.. code-block:: 3d

  typedef struct _WRAPPER(EVERPARSE_COPY_BUFFER_T Output)
  {
      TLV *tlv probe ProbeAndCopy(length=???, destination=Output);
  } WRAPPER;


But, this type is not expressible: when writing a probe, one needs to provide a
``length``, bounding the amount of data to be copied into the ``Output`` buffer.
But, in this case, there is no length to provide.

We could try another approach by expecting the context to bound the length in
advance:

.. code-block:: 3d

  typedef struct _UNION(UINT8 tag) {
      switch (tag) {
          case 0:
              UINT8 case0;
          case 1:
              UINT16 case1;
          default: 
              UINT32 other;
      } field;
  } UNION;

  typedef struct _TLV(UINT32 Len)
  {
      UINT8 tag;
      UINT32 length { length == Len };
      UNION(tag) payload[:byte-size length];
  } TLV;

  typedef struct _WRAPPER(UINT32 Len, EVERPARSE_COPY_BUFFER_T Output)
  where (Len > 5) 
  {
      TLV(Len - 5) *tlv probe ProbeAndCopy(length=Len, destination=Output);
  } WRAPPER;


This works: if the caller can bound the entire size of the pointed to data and
pass it to ``WRAPPER`` as a parameter ``Len``, then we can use that as a bound.

However, if now we try to specialize ``WRAPPER`` as follows:

.. code-block:: 3d

  specialize (pointer(*), pointer(UINT32)) WRAPPER WRAPPER_32;

We get the following error:

.. code-block:: text

  ./SpecializeDep1.3d:(22,11): (Error) Cannot coerce a type with data-dependency; 
    field payload of type SpecializeDep1.UNION(tag) may depend on the field `tag`

That is, in order to coerce a ``UNION(tag)`` from a 32- to 64-bit
representation, in genneral, a coercion would have to read the ``tag`` field of
``TLV``, then branch on it, and then coerce each case of ``UNION`` accordingly.
As mentioned earlier, coercions cannot depend on the data being coerced---so 3d
rejects this specification.

Note, in this case, one could argue that ``UNION(tag)`` has the same
representation in 32- and 64-bits, so 3d could accept the specification:
however, 3d does not yet recognize such special cases.

One could play the same game again, and try to get the caller to provide the
``tag`` as a parameter (although as we do this, increasingly, the caller has to
be able to predict the cases of the data). The listing below works:

.. literalinclude:: SpecializeDep1.3d
  :language: 3d
  :start-after: //SNIPPET_START: main$
  :end-before: //SNIPPET_END: main$

However, we remark on a few points:

  * First, this specification is far from ideal, since it requires the caller to
    predict both the ``tag`` and ``length`` of the TLV message.

  * Second, 3d's determination of data dependence is a syntactic criterion:
    notice how we have changed the type of the payload field to only mention the
    parameters in scope, rather than the fields.

    .. code-block:: 3d

      UNION(Expected) payload[:byte-size Len];

Note, one does not always need the calling context to pass in arguments like
``Len`` or ``Expected``: these just need to be values in scope at the point at
which the probe is used. For instance, the following would work too, for a
pointer to a variable length array, each of whose elements is a ``UNION(tag)``:

.. literalinclude:: SpecializeDep1.3d
  :language: 3d
  :start-after: //SNIPPET_START: alt$
  :end-before: //SNIPPET_END: alt$


Data Dependency for Well-formedness
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

There is another form of data dependency that is also not supported: dependence
on data constraints that ensure well-formedness of specifications. The following
variant of our previous example illustrates.

.. code-block:: 3d

  typedef struct _TLV(UINT8 Expected, UINT16 Len)
  {
      UINT8 tag { tag == Expected };
      UINT32 length { Len > 5 && length == Len - 5 };
      UNION(Expected) payload[:byte-size (Len - 5)];
  } TLV;

  typedef struct _WRAPPER(UINT8 Expected, UINT16 Len, EVERPARSE_COPY_BUFFER_T Output)
  {
      TLV(Expected, Len) *tlv
          probe ProbeAndCopy(length=Len, destination=Output);
  } WRAPPER;

In this variant, rather than constrain ``Len > 5`` in the ``Wrapper``, we add a
constraint on the ``length`` field enforcing ``Len > 5``, and then using ``Len -
5`` for the length of ``payload``---the constraint ensures that the subtraction
``Len - 5`` does not underflow.

However, if we try to specialize ``WRAPPER`` to 32 bits:

.. code-block:: 3d

  specialize (pointer(*), pointer(UINT32)) WRAPPER WRAPPER_32;

We get the following *verification* error:

.. code-block:: text

  * Error 19 at out/SpecializeDep1Fail.fst(195,2-205,63):
  - Cannot verify u16 subtraction
  - The SMT solver could not prove the query. Use --query_stats for more
    details.
  - Also see: SpecializeDep1Fail.3d(22,40-22,40)

3d accepts the specification and then translates it to F* for well-formedness
checking: but F* rejects the specification saying it cannot prove that the
subtraction ``Len - 5`` does not underflow. This is because, again, the coercion
of ``TLV`` from 32- to 64-bits is not data dependent, and as such, the
constraint on the ``length`` field is not enforced by the coercion, and F*
rightfully rejects the subtraction as unsafe.


And End-to-end Example with Variable-length Structures
.......................................................

Although data dependency is forbidden in coercions, there are many cases where
variable-length structures fit well with 3d's support for auto-specialization.

A small but fully worked out example `of specialization with variable-length
structures is available in the EverParse repository
<https://github.com/project-everest/everparse/tree/master/src/3d/tests/specialize_test2>`_, 
including a main file driving the generated code with test input.



Other forms of Specialization
.............................

Today, 3d only supports specialized 64-bit pointer types to 32-bit pointers. In
the future, we envision adding support for other forms of specialization, e.g.,
automatically specializing little-endian to big-endian types.


Comments
--------

The user can insert comments in their ``.3d`` file, some of which will
be inserted into the ``.c`` file:

There are three kinds of comments:

* Block comments are delimited by ``/*`` and ``*/`` and do not
  nest. These are never propagated to the C code.
  
* Line comments begin with ``//`` and are propagated to C
  heuristically close to the translated source construct.
  
* Each top-level declaration can be preceded by a type declaration
  comment delimited by ``/*++`` and ``--*/``: These are propagated to
  the C code preceding the C procedure corresponding to the validator
  of the source type.


Adding copyright notices to produced .c/.h files
------------------------------------------------

If, along with some ``MyFile.3d``, in the same directory, you provide
a file ``MyFile.3d.copyright.txt`` that contains syntactically correct
C comments (with ``//`` or ``/* ... */``), then EverParse will prepend
``MyFile.c``, ``MyFileWrapper.c`` and their corresponding ``.h`` with
these comments. You do not need to mention this file on the command
line.

These comments can contain the following special symbols:

* ``EVERPARSEVERSION``, which EverParse will automatically replace
  with its version number;

* ``FILENAME``, which EverParse will automatically replace with the
  name of the ``.c`` / ``.h`` file being generated.

* ``EVERPARSEHASHES``, which EverParse will automatically replace with
  a hash of the contents of the corresponding .3d file for the purpose
  of ``--check_hashes inplace`` or ``--check_inplace_hash`` (see `Hash
  checking <3d.html#alternate-mode-hash-checking>`_).

  
Modular structure and files
---------------------------

A 3d specification is described in a collection of modules, each
stored in a file with a ``.3d`` extension. The name of a module is
derived from its filename, i.e., the file ``A.3d`` defines a module
named ``A``. A module can ``Derived`` (in Derived.3d) can refer to
another module ``Base`` (in Base.3d) by its name, allowing definitions
in ``Derived`` to reuse the definitions that are exported in ``Base``.

For example, in module ``Base`` we could define the following types:

.. literalinclude:: Base.3d
    :language: 3d

Note, the ``export`` qualifier indicate that these definitions may be
referenced from another module. Types that are not exproted (like
``Mine``) are not visible from another module.

In ``Derived`` we can use the type from ``Base`` by referring to it
using a fully qualified name of the form ``<MODULE NAME>.<IDENTIFIER>``.

.. literalinclude:: Derived.3d
   :language: 3d
   :start-after: SNIPPET_START: Triple
   :end-before: SNIPPET_END: Triple


3d also allows defining module abbreviations. For example, using
``module B = Base`` we introduce a shorter name for the module
``Base`` for use within the current module.

.. literalinclude:: Derived.3d
   :language: 3d
   :start-after: SNIPPET_START: Quad
   :end-before: SNIPPET_END: Quad

A commented example is available `in the EverParse repository
<https://github.com/project-everest/everparse/blob/master/src/3d/tests/modules/>`_.

Error handling
--------------

When a validator fails, EverParse supports invoking a user-provided
callback with contextual information about the failure.

An error handling callback is a C procedure with the following signature:

.. code-block:: c

  typedef void (*ErrorHandler)(
    const char *TypeName,
    const char *FieldName,
    const char *ErrorReason,
    uint64_t ErrorCode,
    uint8_t *Context,
    uint32_t Length,
    uint8_t *Base,
    uint64_t StartPosition,
    uint64_t EndPosition
  );
    
Every EverParse validator is parameterized by:

* A function pointer, of type ``ErrorHandler``
* A context parameter, ``uint8_t* Context``

At the top-level, when calling into EverParse from an application, one
can instantiate both the ``ErrorHandler`` with a function of one's
choosing and the ``Context`` argument with a pointer to some
application-specific context.

The ``ErrorHandler`` expects

  * The ``Base`` and ``Context`` pointers to refer to live and
    disjoint pieces of memory.

  * For ``Length`` to be the length in bytes of valid memory pointed
    to by ``Base`` and for ``StartPosition <= EndPosition <= Length``.

The ``ErrorHandler`` can

  * Read from all the pointers

  * May only modify the memory reference by ``Context``.

When validating a field ``f`` in a type ``T``, in case the validator
fails, EverParse calls the user-provided ``ErrorHandler``, passing in
the following arguments:

  * The ``TypeName`` argument is the name of the type ``T``

  * The ``FieldName`` argument is name of the field ``f``

  * The ``ErrorReason`` and ``ErrorCode`` arguments are related and can be one of the following pairs:
    
    - "generic error", ``EVERPARSE_ERROR_GENERIC`` (1uL)
    - "not enough data", ``EVERPARSE_ERROR_NOT_ENOUGH_DATA`` (2uL)
    - "impossible", ``EVERPARSE_ERROR_IMPOSSIBLE`` (3uL)
    - "list size not multiple of element size", ``EVERPARSE_ERROR_LIST_SIZE_NOT_MULTIPLE`` (4uL)
    - "action failed", ``EVERPARSE_ERROR_ACTION_FAILED`` (5uL)
    - "constraint failed", ``EVERPARSE_ERROR_CONSTRAINT_FAILED`` (6uL)
    - "unexpected padding", ``EVERPARSE_ERROR_UNEXPECTED_PADDING`` (7uL)
    - "unspecified", with the ``ErrorCode > 7uL``

  * The ``Context`` argument is the user-provided ``Context`` pointer
    
  * The ``Length`` argument is the length in bytes of the input buffer

  * The ``Base`` argument is a pointer to the base of the input buffer

  * The ``StartPosition`` argument is the offset from ``Base`` of the
    start of the field ``f``
  
  * The ``EndPosition`` argument is the offset from ``Base`` of the
    end of the field ``f`` at which the validation failure occurred.
                
Following a validation failure at a given field, EverParse will invoke
the ``ErrorHandler`` at each enclosing type as well. This allows a
caller to reconstruct a stack trace of a failing validation.

EverParse generates a default error handler that records just the
deepest validation failure that occurred.

Fully worked examples: TCP Segment Headers
-------------------------------------------

The classic `IETF RFC 793 <https://tools.ietf.org/html/rfc793>`_ from
1981 introduces the TCP protocol, including the format of the header
of TCP segments. The format has been extended slightly since then, to
accommodate new options and flags---this `Wikipedia page
<https://en.wikipedia.org/wiki/Transmission_Control_Protocol#TCP_segment_structure>`_
provides a good summary. 

Reproduced below is an ASCII depiction of the format of TCP
headers. In this section, we show how to specify this format in
3d. The full specification can be found `here <https://github.com/project-everest/everparse/tree/master/src/3d/tests/tcpip/TCP.3d>`_.


.. code-block:: text

    0                   1                   2                   3
    0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |          Source Port          |       Destination Port        |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                        Sequence Number                        |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                    Acknowledgment Number                      |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |  Data |     |N|C|E|U|A|P|R|S|F|                               |
   | Offset| Rese|S|W|C|R|C|S|S|Y|I|            Window             |
   |       | rved| |R|E|G|K|H|T|N|N|                               |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |           Checksum            |         Urgent Pointer        |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                    Options                    |    Padding    |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   |                             data                              |
   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+


Each ``-`` in the diagram represents a single bit, with fioelds
separated by vertical bars ``|``.

The main subtle element of the specification is the handling of the
``DataOffset`` field. It is a 4-bit value representing an offset from
the beginning of the segment, in 32-bit increments, of the start of
the ``data`` field. The ``Options`` and ``Padding`` fields are
optional, so the ``DataOffset`` field is used to encode the size of
the ``Options`` field. As such, ``DataOffset`` is always at least
``5``.

The ``Options`` field itself is an array of tagged unions,
representing various kinds of options. Padding and the end of the
options array ensures that the ``data`` fields is always begins at a
multiple of 32-bits from the start of the segment.

Additionally, semantic constraints restrict the values of the fields
depending on the values of some other fields. For example, the
Acknowledgement number can only be non-zero when the ``ACK`` bit is
set.

To specify the type of a TCP header, we begin by defining some basic
types.

.. code-block:: 3d

  typedef UINT16 PORT;
  typedef UINT32 SEQ_NUMBER;
  typedef UINT32 ACK_NUMBER;
  typedef UINT16 WINDOW;
  typedef UINT16 CHECK_SUM;
  typedef UINT16 URGENT_PTR;

The source and destination port each occupy 16 bits and are
represented by a ``UINT16``; the sequence and acknowledgment number
fields are ``UINT32`` etc.

Next, we define the various kind of options that are allowed. Every
option begins with an option kind tag, an 8-bit value. Depending on
the option kind, a variable number of bits of an option value can
follow. The permitted option kinds are:

.. code-block:: 3d

  #define OPTION_KIND_END_OF_OPTION_LIST 0x00
  #define OPTION_KIND_NO_OPERATION 0x01
  #define OPTION_KIND_MAX_SEG_SIZE 0x02
  #define OPTION_KIND_WINDOW_SCALE 0x03
  #define OPTION_KIND_SACK_PERMITTED 0x04
  #define OPTION_KIND_SACK 0x05
  #define OPTION_KIND_TIMESTAMP 0x08

An ``OPTION`` is parameterized by a boolean, ``MaxSegSizeAllowed``,
which constraints when the ``OPTION_KIND_MAX_SEG_SIZE`` is allowed to
be present---it turns out, the ``SYN`` bit in the header must be set
for this option to be allowed. The general shape of an ``OPTION`` is
as below.

.. code-block:: 3d

  typedef struct _OPTION(Bool MaxSegSizeAllowed)
  {
      UINT8 OptionKind;
      OPTION_PAYLOAD(OptionKind, MaxSegSizeAllowed) OptionPayload;
  } OPTION;

We have an ``OptionKind`` field followed by an ``OptionPayload`` that
depends on the ``OptionKind`` and the ``MaxSegSizeAllowed`` flag.

Next, to define the ``OPTION_PAYLOAD`` type, we use a ``casetype``, as
shown below.

.. code-block:: 3d

  casetype _OPTION_PAYLOAD(UINT8 OptionKind, Bool MaxSegSizeAllowed)
  {
    switch(OptionKind)
    {
     case OPTION_KIND_END_OF_OPTION_LIST:
       unit EndOfList;
       
     case OPTION_KIND_NO_OPERATION:
       unit Noop;

     case OPTION_KIND_MAX_SEG_SIZE:
       MAX_SEG_SIZE_PAYLOAD(MaxSegSizeAllowed) MaxSegSizePayload;

     case OPTION_KIND_WINDOW_SCALE:
       WINDOW_SCALE_PAYLOAD WindowScalePayload;

     case OPTION_KIND_SACK_PERMITTED:
       UINT8 SackPermittedPayload;

     case OPTION_KIND_SACK:
       SELECTIVE_ACK_PAYLOAD SelectiveAckPayload;

     case OPTION_KIND_TIMESTAMP:
       TIMESTAMP_PAYLOAD TimestampPayload;
    } 
  } OPTION_PAYLOAD;

In the first two cases of ``OptionKind``, no payload is expected. The
``unit`` type in 3d is an empty type---it consumes no space in the
message format.

For ``OPTION_KIND_MAX_SEG_SIZE``, we have the following payload---the
use of the ``where` constraint ensures that this case is present only
when `MaxSegSizeAllowed == true``. The payload is a length field (4
bytes) and a 2-byte ``MaxSegSize`` value.

.. code-block:: 3d

  typedef struct _MAX_SEG_SIZE_PAYLOAD(Bool MaxSegSizeAllowed)
  where MaxSegSizeAllowed
  {
    UINT8 Length
    {
      Length == 4
    };
    UINT16 MaxSegSize;
  } MAX_SEG_SIZE_PAYLOAD;

The other cases are relatively straightforward, where
``SELECTIVE_ACK_PAYLOAD`` and ``TIMESTAMP_PAYLOAD`` illustrate the use
of variable length arrays.

.. code-block:: 3d

  typedef struct _WINDOW_SCALE_PAYLOAD
  {
    UINT8 Length
    {
      Length == 3
    };
    UINT8 WindowScale;
  } WINDOW_SCALE_PAYLOAD;


  typedef struct _SELECTIVE_ACK_PAYLOAD
  {
    UINT8 Length
    {
      Length == 10 ||
      Length == 18 ||
      Length == 26 ||
      Length == 34
    };
    UINT8 SelectiveAck[:byte-size (Length - 2)];
  } SELECTIVE_ACK_PAYLOAD;

  
  typedef struct _TIMESTAMP_PAYLOAD
  {
    UINT8 Length
    {
      Length == 10
    };
    UINT8 TimeStamp[:byte-size (Length - 2)];
  } TIMESTAMP_PAYLOAD;

Finally, we can assemble our top-level TCP header type, as shown
below. The specification of the options array is weaker than it could
be. It currently permits an end-of-options-list option to appear
anywhere in the Options list, rather than as just the last
element. This can be improved by using a more advanced combinator from
EverParse, however we leave it as is for simplicity of this example.

.. code-block:: 3d

  /*++
    The top-level type of a TCP Header

    Arguments:

    * UINT32 SegmentLength, the size of the segment,
      including both header and data, passed in by the caller

    --*/
  entrypoint
  typedef struct _TCP_HEADER(UINT32 SegmentLength)
  {
    PORT            SourcePort;
    PORT            DestinationPort;
    SEQ_NUMBER      SeqNumber;
    ACK_NUMBER      AckNumber;
    UINT16          DataOffset:4
    { //DataOffset is in units of 32 bit words
      sizeof(this) <= DataOffset * 4 && //DataOffset points after the static fields
      DataOffset * 4 <= SegmentLength //and within the current segment
    };
    UINT16          Reserved:3
    {
      Reserved == 0 //Reserved bytes are unused
    };
    UINT16          NS:1;
    UINT16          CWR:1;
    UINT16          ECE:1;
    UINT16          URG:1;
    UINT16          ACK:1
    {
      AckNumber == 0 ||
      ACK == 1 //AckNumber can only be set if the ACK flag is set
    } ;
    UINT16          PSH:1;
    UINT16          RST:1;
    UINT16          SYN:1;
    UINT16          FIN:1;
    WINDOW          Window;
    CHECK_SUM       CheckSum;
    URGENT_PTR      UrgentPointer
    {
      UrgentPointer == 0 ||
      URG == 1 //UrgentPointer can only be set if the URG flag is set
    };
    //The SYN=1 condition indicates when MAX_SEG_SIZE option can be received
    //This is an array of options consuming
    OPTION(SYN==1)  Options[:byte-size (DataOffset * 4) - sizeof(this)];
    UINT8           Data[SegmentLength - (DataOffset * 4)];
  } TCP_HEADER;

  
The type is parameterized by ``SegmentLength``, the size in bytes
determined by the caller of the entire segment, including the header
and the data.

The first four fields, ``SourcePort``, ``DestinationPort``,
``SeqNumber`` and ``AckNumber`` are straightforward.

The ``DataOffset`` field is 4-bit value constrained to point beyond
the static fields of the header. Here ``sizeof(this)`` is a 3d
compile-time constant referring to the size of the non-variable length
prefix of the current type, i.e., the sum of the length in bytes of
all the fields up to the ``Options`` field. In this case, that number
is ``20``. ``DataOffset`` is also constrained to reference an offset
within the curent segment.

Next, we have 3 reserved bits, following by 1 bit each for the 9
flags. The ``Ack`` flag is interesting, since its constraints states
that the ``AckNumber`` can be non-zero only if the ``Ack`` bit is set.

Then, we have a ``Window`` and ``CheckSum``, both of which are
straightforward. Note, we do not specify the ``CheckSum`` as part of
the format---that's up to an application-specific check to
confirm. Alternatively, one could check this using a user-provided
action callback, though this is not yet supported.

The ``UrgentPointer`` field is similar to ``AckNumber`` in that it can
only be non-zero when the ``URG`` flag is set.

Then, we have an ``Options`` array, using the condition ``SYN==1`` to
determine the ``MaxSegSizeAllowed`` condition. The size in bytes of
the options array is variable and includes also the padding field, to
ensure 32-bit alignment. Note, this type is little too permissive, as
it will permit options arrays where the end-of-list option kind is not
necessarily only the last element.

Finally, we have the data field itself, whose byte size is bytes is
the computed expression.

Generated code
..............

Running the EverParse toolchain on the TCP segment header
specification produces a C procedure with the following signature, in ``TCPWrapper.h``:


.. code-block:: c

   BOOLEAN TcpCheckTcpHeader(uint32_t ___SegmentLength, uint8_t *base, uint32_t len);

This procedure is a validator for the ``TCP_HEADER`` type. The caller
passes in three parameters:

* ``__SegmentLength``, representing the ``SegmentLength`` argument of
  the ``TCPHeader`` type in the 3d specification.

* ``base``: a pointer to an array of bytes

* ``len``: a lower bound on the length of that array that ``base``
  points to.

``TcpCheckTcpHeader`` returns ``TRUE`` if, and only if, the contents
of ``base`` represent a valid ``TCPHeader``, while enjoying all the
guarantees of memory safety, arithmetic safety, double-fetch freedom,
not modifying any of the caller's memory, not allocating any heap
data, and being provably functional correct.

Error handling
..............

``TCPWrapper.h`` includes a default error handler to report the leaf
validation failure. It also expects a client module to supply an
implementation of

.. code-block:: c

   void TcpEverParseError(
        const char *TypeName,
        const char *FieldName,
        const char *Reason,
        uint64_t ErrorCode)
                

This can be instantiated with a procedure to, say, log an error.

Alternatively, the default error handler in ``TCPWrapper.h`` can be
replaced by a custom error handler of your choosing.


Fully worked examples: ELF files
---------------------------------

ELF (Executable and Linkable Format) is a common, standard file format
for various kinds of binary files (object files, executables, shared
libraries, and core dumps). The file format is described as
C-structures in the `elf.h
<https://man7.org/linux/man-pages/man5/elf.5.html>`_ file.

In this section we develop (parts of) a 3d specification for 64-bits
ELF files and describe how it can be integrated in existing projects
for validating potentially untrusted ELF files. A complete ELF
specification can be found in the `3d test suite
<https://github.com/project-everest/everparse/blob/master/src/3d/tests/ELF.3d>`_.

An ELF file consists of an ELF header, followed by a program header
table and a section header table. Both the tables are optional and
describe the rest of the ELF file. The ELF header specifies the
offsets and the number of entries in each of the tables. One
interesting aspect of validating ELF files is then to check that both
the tables contain the specified number of entries and point to the
valid parts of the rest of the ELF file.

The ELF header starts with a 16 byte array. The first four bytes of
the array are fixed: 0x7f, followed by 'E', 'L', and 'F'. Other bytes
of the array specify the binary architecture (32-bits or 64-bits),
endianness, ELF specification version, target OS, and ABI version of
the file. The last 7 bytes of the array are padding bytes set to 0. To
be able to constrain the individual bytes of this array, we specify in
3d as a struct.

.. code-block:: 3d

  typedef struct _E_IDENT
  {
    UCHAR    ZERO    { ZERO == 0x7f };
    UCHAR    ONE     { ONE == 0x45 };
    UCHAR    TWO     { TWO == 0x4c };
    UCHAR    THREE   { THREE == 0x46 };
  
    //This 3d spec applies to 64-bit only currently
    ELFCLASS FOUR    { FOUR == ELFCLASS64 };
    
    ELFDATA  FIVE;
  
    //ELF specification version is always set to 1
    UCHAR    SIX     { SIX == 1 };
  
    ELFOSABI SEVEN;
  
    //ABI version, always set to 0
    ZeroByte EIGHT;
  
    //padding, remaining 7 bytes are 0
    ZeroByte NINE_FIFTEEN[E_IDENT_PADDING_SIZE];
  } E_IDENT;

(The omitted definitions can be found in the `full development
<https://github.com/project-everest/everparse/blob/master/src/3d/tests/ELF.3d>`_.)


Following this 16 byte array, the ELF header specifies the file type,
file version, followed by fields of our interest: ``E_PHOFF``,
``E_SHOFF`` (offsets of the two tables), and ``E_PHNUM``, ``E_SHNUM``
(number of entries in the two tables).

.. code-block:: 3d

  // ELF HEADER BEGIN

  E_IDENT          IDENT;
  ELF_TYPE         E_TYPE       { E_TYPE != ET_NONE };

  UINT16           E_MACHINE;
  UINT32           E_VERSION    { E_VERSION == 1 };
  ADDRESS          E_ENTRY;

  //Program header table offset
  OFFSET           E_PHOFF;

  //Section header table offset
  OFFSET           E_SHOFF;
  
  UINT32           E_FLAGS;

  UINT16           E_EHSIZE     { E_EHSIZE == sizeof (this) };

  UINT16           E_PHENTSIZE;

  //Number of program header table entries
  UINT16           E_PHNUM
    { (E_PHNUM == 0 && E_PHOFF == 0) ||  //no Program Header table
      (0 < E_PHNUM && E_PHNUM < PN_XNUM &&
       sizeof (this) == E_PHOFF &&  //Program Header table starts immediately after the ELF Header
       E_PHENTSIZE == sizeof (PROGRAM_HEADER_TABLE_ENTRY)) };
  
  UINT16           E_SHENTSIZE;

  //Number of section header table entries
  UINT16           E_SHNUM
    { (E_SHNUM == 0 && E_SHOFF == 0) ||  // no Section Header table
      (0 < E_SHNUM && E_SHNUM < SHN_LORESERVE &&
       E_SHENTSIZE == sizeof (SECTION_HEADER_TABLE_ENTRY)) };

  //Section header table index of the section names table
  UINT16           E_SHSTRNDX
    { (E_SHNUM == 0 && E_SHSTRNDX == SHN_UNDEF) ||
      (0 < E_SHNUM  && E_SHSTRNDX < E_SHNUM) };
	
  // ELF HEADER END


The constraint on ``E_PHNUM`` enforces that either the file has no
program header table (``E_PHNUM == 0 && E_PHOFF == 0``) or the table
has non-zero number of entries and it starts immediately after the ELF
header (``sizeof (this)`` for the encapsulating struct type refers to
the ELF header shown here). We add similar constraints to ``E_SHNUM``
but do not add any check for ``E_SHOFF``, since unlike the
program header table, the section header table does not have a fixed
offset.

The ELF header is followed by the two optional tables. We specify
these optional tables using ``casetype``. First, the program header
table:

.. code-block:: 3d

  casetype _PROGRAM_HEADER_TABLE_OPT (UINT16 PhNum,
    				      OFFSET ElfFileSize)
  {
    switch (PhNum)
    {
      case 0:
        unit    Empty;
      default:
        PROGRAM_HEADER_TABLE_ENTRY(ElfFileSize)    Tbl[:byte-size sizeof (PROGRAM_HEADER_TABLE_ENTRY) * PhNum]
     }
  } PROGRAM_HEADER_TABLE_OPT;


The type ``PROGRAM_HEADER_TABLE_OPT`` is parameterized by
the number of program header table entries, as specified in the ELF
header, and the size of the ELF file; the latter allows us to check
that the segments pointed to by the program header table entries are in 
the file range.

In case ``PhNum`` is 0, the type is the empty ``unit``
type. Otherwise, it is an ``PROGRAM_HEADER_TABLE_ENTRY`` array of
size ``sizeof (PROGRAM_HEADER_TABLE_ENTRY) * PhNum`` bytes where the type
``PROGRAM_HEADER_TABLE_ENTRY`` describes a segment:


.. code-block:: 3d

  typedef struct _PROGRAM_HEADER_TABLE_ENTRY (OFFSET ElfFileSize)
  {
    UINT32    P_TYPE;

    UINT32    P_FLAGS  { P_FLAGS <= 7 };

    OFFSET    P_OFFSET;

    ADDRESS   P_VADDR;

    ADDRESS   P_PADDR;

    //The constraint checks that the segment is in the file range
    UINT64    P_FILESZ  { P_FILESZ < ElfFileSize &&
                          P_OFFSET <= ElfFileSize - P_FILESZ };
    UINT64    P_MEMSZ;

    UINT64    P_ALIGN;
  } PROGRAM_HEADER_TABLE_ENTRY;


The specification of the section header table is also a ``casetype``:

.. code-block:: c

  casetype _SECTION_HEADER_TABLE_OPT (OFFSET PhTableEnd,
                                      OFFSET ShOff,
                                      UINT16 ShNum,
  				      OFFSET ElfFileSize)
  {
    switch (ShNum)
    {
      case 0:
        NO_SECTION_HEADER_TABLE(PhTableEnd, ElfFileSize)                   NoTbl;      

      default:
        SECTION_HEADER_TABLE(PhTableEnd, ShOff, ShNum, ElfFileSize)        Tbl;
    }
  } SECTION_HEADER_TABLE_OPT;


We parameterize this type by the
offset where the program header table ends, the section header table
offset, number of section header table entries, and the size of the
file.

When number of entries is 0, the file does not have a section header
table, but we still need to check that the file contains enough bytes
after the program header table so that its total size is
``ElfFileSize``. ``NO_SECTION_HEADER_TABLE`` specifies such a type:

.. code-block:: 3d

  typedef struct _NO_SECTION_HEADER_TABLE (OFFSET PhTableEnd,
  					   UINT64 ElfFileSize)
  where (PhTableEnd <= ElfFileSize && ElfFileSize - PhTableEnd <= MAX_UINT32)
  {
    UINT8        Rest[:byte-size (UINT32) (ElfFileSize - PhTableEnd)];
  } NO_SECTION_HEADER_TABLE;


The checks in the ``where`` clause ensure safety of the arithmetic
operations.

In case the section header table is non-empty, we specify (a) the
bytes between the end of the program header table and the beginning of
the section header table, (b) the section header table, and (c) final
check that end of the section header table is the end of the file.

.. code-block:: 3d

  typedef struct _SECTION_HEADER_TABLE (OFFSET PhTableEnd,
                                        UINT64 ShOff,
                                        UINT16 ShNum,
				        OFFSET ElfFileSize)
  where (PhTableEnd <= ShOff && ShOff - PhTableEnd <= MAX_UINT32)
  {
    UINT8        PHTABLE_SHTABLE_GAP[(UINT32) (ShOff - PhTableEnd)];

    SECTION_HEADER_TABLE_ENTRY(ShNum, ElfFileSize)    SHTABLE[:byte-size sizeof (SECTION_HEADER_TABLE_ENTRY) * ShNum];

    // Check that we have consumed all the bytes in the file
    unit        EndOfFile
    {:on-success var x = field_pos; return (x == ElfFileSize); };  
  } SECTION_HEADER_TABLE;


The section header table, similar to the program header table, is an
array of entries.
  
Finally, the top-level ELF format:

.. code-block:: 3d


  entrypoint
  typedef struct _ELF (UINT64 ElfFileSize)
  {
    ... //ELF header as above

    //Optional Program Header table
    PROGRAM_HEADER_TABLE_OPT (E_PHNUM,
			      ElfFileSize)            PH_TABLE;

    //Optional Section Header Table
    //Recall that the first argument is the end of the program header table
    SECTION_HEADER_TABLE_OPT ((E_PHNUM == 0) ? E_EHSIZE : E_PHOFF + (sizeof (PROGRAM_HEADER_TABLE_ENTRY) * E_PHNUM),
                              E_SHOFF,
                              E_SHNUM,
			      ElfFileSize)            SH_TABLE;
  } ELF;


Integrating ELF validator in existing code
...........................................

To compile the 3d specification to C code, download the latest
`EverParse release
<https://github.com/project-everest/everparse/releases>`_ and compile
the 3d spec with the EverParse binary, e.g. for Windows:
``everparse.cmd --batch ELF.3d``. This command generates
``ELFWrapper.h`` and ``ELFWrapper.c`` files, with the top-level
validation function as follows:

.. code-block:: c

  BOOLEAN ElfCheckElf(uint64_t ___ElfFileSize, uint8_t *base, uint32_t len);

The actual validator implementation is generated in ``ELF.c``. To
integrate these validators into existing C code, drop in these
generated ``.c`` and ``.h`` files
in the development and invoke ```ElfCheckElf`` as necessary.


