
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

--Type class, takes a Type and returns a type
#check Add      --Type -> Type
#check Add Nat  --Type
--Each instance of the type has a diffrent version
--of the add method, allowing for overrieds
#check @Add.add Nat
#check @Add.add (PPoint Nat)
--To select which varient of Add.add the first type
--paramter is used. The [self : Add α] 
--enforces that an instance for Add α has been created
--and finds it and uses it. 

--Monad takes a map of types from U1 to U2 and maps them to
--A new type in U=max(U1+1, U2) 
#check Option
#check Monad Option
#check Monad List 





#check Option Empty
#check Option.some 