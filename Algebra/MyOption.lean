inductive my_option (t: Sort α) where
  | none
  | some (value: t)

def my_option.is_some (o: my_option α) : Prop := match o with
  | .none => False
  | .some _ => True

def my_option.map (o: my_option α) : (α -> β) -> my_option β := fun f => match o with
  | .none => .none
  | .some x => .some <| f x

def my_option.bind (o: my_option α) : (α -> my_option β) -> my_option β := fun f => match o with
  | .none => .none
  | .some x => f x
