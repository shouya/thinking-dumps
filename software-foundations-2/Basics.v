Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday.

 Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  end.



