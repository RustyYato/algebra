structure Set (α: Type _) where
  ofMem ::
  mem : α -> Prop

instance : Membership α (Set α) := ⟨fun a b => Set.mem b a⟩

def Set.univ α : Set α := .ofMem fun _ => True
def Set.empty α : Set α := .ofMem fun _ => False

instance : EmptyCollection (Set α) := ⟨Set.empty α⟩
