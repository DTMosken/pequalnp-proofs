import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1641

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

abbrev good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma value_mono {n : ℕ} (C : Circuit) (hG : good C)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · intro hx
      have hfx := gate_value C x w (by omega) hw
      have hfy := gate_value C y w (by omega) hw
      rw [hfx] at hx
      rw [hfy]
      obtain ⟨hop, _⟩ := hG (C.gates[w - n]'(by unfold Circuit.size at hw; omega)) (List.getElem_mem _)
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
        rintro b ⟨r, hr, rfl⟩
        by_cases hrt : r < w
        · simpa [hrt] using ih r hrt (by simpa [hrt] using hx _ ⟨r, hr, rfl⟩)
        · have := hx _ ⟨r, hr, rfl⟩
          simp [hrt] at this
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
        obtain ⟨_, ⟨r, hr, rfl⟩, hv⟩ := hx
        by_cases hrt : r < w
        · exact ⟨_, ⟨r, hr, rfl⟩, by simpa [hrt] using ih r hrt (by simpa [hrt] using hv)⟩
        · simp [hrt] at hv
    · simp [missing_value C x w (by omega)]

abbrev wireValue {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn x)

lemma wire_input {n : ℕ} (gs : List Gate) (p : Fin n) (x : Fin n → Bool) :
    wireValue gs p x = x p := input_value ⟨gs, 0⟩ x p

lemma wire_mono {n : ℕ} (gs : List Gate) (hG : good ⟨gs, 0⟩)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    wireValue gs w x = true → wireValue gs w y = true := value_mono ⟨gs, 0⟩ hG x y hxy w

lemma wire_or {n : ℕ} (gs : List Gate) (i : Fin gs.length)
    (hop : (gs.get i).op = GateOp.or) (x : Fin n → Bool) :
    wireValue gs (n + (i : ℕ)) x = true ↔
      ∃ r ∈ (gs.get i).inputs, r < n + (i : ℕ) ∧ wireValue gs r x = true :=
  or_value ⟨gs, 0⟩ i i.isLt hop x

lemma wire_or_false_child {n : ℕ} (gs : List Gate) (i : Fin gs.length)
    (hop : (gs.get i).op = GateOp.or) (x : Fin n → Bool) {e : ℕ}
    (he : e ∈ (gs.get i).inputs) (hlt : e < n + (i : ℕ))
    (hf : wireValue gs (n + (i : ℕ)) x = false) : wireValue gs e x = false := by
  cases hx : wireValue gs e x with
  | false => rfl
  | true =>
      have hc := (wire_or gs i hop x).2 ⟨e, he, hlt, hx⟩
      rw [hf] at hc
      contradiction

def OrClosed (n : ℕ) (gs : List Gate) (Z : Set ℕ) : Prop :=
  ∀ i : Fin gs.length, n + (i : ℕ) ∈ Z → (gs.get i).op = GateOp.or →
    ∀ e ∈ (gs.get i).inputs, e ∈ Z

def OrTop (n : ℕ) (gs : List Gate) (w : ℕ) (p : Fin n) : Prop :=
  ∀ Z : Set ℕ, w ∈ Z → OrClosed n gs Z → (p : ℕ) ∈ Z

lemma orTop_self {n : ℕ} (gs : List Gate) (p : Fin n) : OrTop n gs p p :=
  fun _ hp _ => hp

lemma orTop_child {n : ℕ} {gs : List Gate} (i : Fin gs.length)
    (hop : (gs.get i).op = GateOp.or) {e : ℕ} (he : e ∈ (gs.get i).inputs)
    {p : Fin n} (hp : OrTop n gs e p) : OrTop n gs (n + (i : ℕ)) p :=
  fun Z hz hZ => hp Z (hZ i hz hop e he) hZ

lemma orTop_not {n w : ℕ} {gs : List Gate} {p : Fin n} (hne : w ≠ (p : ℕ))
    (hchild : ∀ i : Fin gs.length, w = n + (i : ℕ) → (gs.get i).op = GateOp.or →
      ∀ e ∈ (gs.get i).inputs, ¬ OrTop n gs e p) : ¬ OrTop n gs w p := by
  intro hw
  let B : Set ℕ := {v | ¬ OrTop n gs v p}
  have hB : OrClosed n gs B := by
    intro i hi hop e he hp
    exact hi (orTop_child i hop he hp)
  let Z : Set ℕ := insert w B
  have hZ : OrClosed n gs Z := by
    intro i hi hop e he
    change n + (i : ℕ) ∈ insert w B at hi
    change e ∈ insert w B
    rcases Set.mem_insert_iff.mp hi with eq | hb
    · exact Set.mem_insert_of_mem _ (show e ∈ B from hchild i eq.symm hop e he)
    · exact Set.mem_insert_of_mem _ (hB i hb hop e he)
  have hp := hw Z (Set.mem_insert _ _) hZ
  change (p : ℕ) ∈ insert w B at hp
  rcases Set.mem_insert_iff.mp hp with hp | hp
  · exact hne hp.symm
  · exact hp (orTop_self gs p)

lemma orTop_raw {n : ℕ} (gs : List Gate) (r p : Fin n) :
    OrTop n gs r p ↔ r = p := by
  constructor
  · intro hr
    by_contra hn
    have hs : (r : ℕ) ≠ (p : ℕ) := fun e => hn (Fin.ext e)
    exact orTop_not hs (by intro i heq; omega) hr
  · rintro rfl
    exact orTop_self gs r

lemma orTop_gate {n : ℕ} (gs : List Gate) (i : Fin gs.length) (p : Fin n) :
    OrTop n gs (n + (i : ℕ)) p ↔
      (gs.get i).op = GateOp.or ∧ ∃ e ∈ (gs.get i).inputs, OrTop n gs e p := by
  constructor
  · intro hw
    classical
    by_contra! hn
    exact orTop_not (by omega) (by
      intro k hk hop e he hp
      have eq : i = k := Fin.ext (Nat.add_left_cancel hk)
      subst k
      exact hn hop e he hp) hw
  · rintro ⟨hop, e, he, hp⟩
    exact orTop_child i hop he hp

lemma orTop_cases {n w : ℕ} {gs : List Gate} {p : Fin n} (hw : OrTop n gs w p) :
    w = (p : ℕ) ∨ ∃ i : Fin gs.length, w = n + (i : ℕ) ∧ (gs.get i).op = GateOp.or ∧
      ∃ e ∈ (gs.get i).inputs, OrTop n gs e p := by
  classical
  by_contra! hn
  exact orTop_not hn.1 (by
    intro i hi hop e he hs
    exact hn.2 i hi hop e he hs) hw

lemma orTop_true {n : ℕ} (gs : List Gate)
    (earlier : ∀ i : Fin gs.length, ∀ e ∈ (gs.get i).inputs, e < n + (i : ℕ))
    (x : Fin n → Bool) {p : Fin n} (hx : x p = true) (w : ℕ) (hw : OrTop n gs w p) :
    wireValue gs w x = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases orTop_cases hw with eq | ⟨i, eq, hop, e, he, hs⟩
    · rw [eq, wire_input]
      exact hx
    · subst w
      have hearlier := earlier i e he
      exact (wire_or gs i hop x).2 ⟨e, he, hearlier, ih e hearlier hs⟩

lemma orTop_singleton {n : ℕ} (gs : List Gate)
    (earlier : ∀ i : Fin gs.length, ∀ e ∈ (gs.get i).inputs, e < n + (i : ℕ))
    {w : ℕ} {p : Fin n} (hw : OrTop n gs w p) :
    wireValue gs w (fun q => decide (q = p)) = true :=
  orTop_true gs earlier _ (by simp) w hw

end PEqualNP.Outside.L_meta_1641

namespace PEqualNP.Outside.L_meta_1641

open PEqualNP.CircuitLowerBounds

abbrev offLine {n : ℕ} (L : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∉ L)

abbrev pointBit {n : ℕ} (p v : Fin n) : Bool := decide (v = p)

lemma singleton_mem_of_off_false {n : ℕ} (gs : List Gate) (goodG : good ⟨gs, 0⟩)
    (L : Finset (Fin n)) (w : ℕ) (p : Fin n)
    (hf : wireValue gs w (offLine L) = false)
    (hp : wireValue gs w (pointBit p) = true) : p ∈ L := by
  by_contra h
  have hle : ∀ v : Fin n, pointBit p v = true → offLine L v = true := by
    intro v hv
    have he : v = p := of_decide_eq_true hv
    subst v
    exact decide_eq_true h
  have ht := wire_mono gs goodG (pointBit p) (offLine L) hle w hp
  rw [hf] at ht
  contradiction

abbrev cleanG {n : ℕ} (gs : List Gate) (M : Finset (Fin n)) (i : Fin gs.length) : Prop :=
  (gs.get i).op = GateOp.or ∧ wireValue gs (n + i.val) (offLine M) = false

abbrev hotW {n : ℕ} (gs : List Gate) (p0 p1 : Fin n) (w : ℕ) : Prop :=
  wireValue gs w (pointBit p0) = true ∨ wireValue gs w (pointBit p1) = true

abbrev topG {n : ℕ} (gs : List Gate) (i : Fin gs.length) (p : Fin n) : Prop :=
  OrTop n gs (n + i.val) p

lemma subsingleton_of_off_false {n : ℕ} (gs : List Gate) (goodG : good ⟨gs, 0⟩)
    (M H : Finset (Fin n)) (hcard : (M ∩ H).card = 1)
    (w : ℕ) (hf : wireValue gs w (offLine H) = false) {p p' : Fin n}
    (hMp : p ∈ M) (hMp' : p' ∈ M)
    (hp : wireValue gs w (pointBit p) = true) (hp' : wireValue gs w (pointBit p') = true) : p = p' := by
  by_contra hne
  have hHp := singleton_mem_of_off_false gs goodG H w p hf hp
  have hHp' := singleton_mem_of_off_false gs goodG H w p' hf hp'
  have hs : ({p, p'} : Finset (Fin n)) ⊆ M ∩ H := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hMp, hHp⟩
    · exact Finset.mem_inter.mpr ⟨hMp', hHp'⟩
  have h := Finset.card_le_card hs
  rw [hcard] at h
  have hc : ({p, p'} : Finset (Fin n)).card = 2 := by simp [hne]
  omega

end PEqualNP.Outside.L_meta_1641

namespace PEqualNP.Outside.L_meta_1641

lemma telescope_unanchored {n : ℕ} (score : ℕ → ℕ) (paid : Finset (Fin n))
    (step : ∀ g : Fin n, score g ≤ score (g.val + 1) + 1)
    (free : ∀ g : Fin n, g ∉ paid → score g = score (g.val + 1)) :
    score 0 ≤ paid.card + score n := by
  classical
  have upto (k : ℕ) (hk : k ≤ n) :
      score 0 ≤ (paid.filter (fun j => j.val < k)).card + score k := by
    induction k with
    | zero => simp
    | succ k ih =>
      let g : Fin n := ⟨k, by omega⟩
      have prev := ih (by omega)
      by_cases h : g ∈ paid
      · have update : paid.filter (fun j => j.val < k + 1) =
            insert g (paid.filter (fun j => j.val < k)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hj, hlt⟩
            by_cases he : j.val = k
            · exact Or.inl (Fin.ext he)
            · exact Or.inr ⟨hj, by omega⟩
          · rintro (rfl | ⟨hj, hlt⟩)
            · exact ⟨h, Nat.lt_succ_self k⟩
            · exact ⟨hj, by omega⟩
        rw [update, Finset.card_insert_of_notMem (by simp [g])]
        have hstep : score k ≤ score (k + 1) + 1 := step g
        omega
      · have update : paid.filter (fun j => j.val < k + 1) = paid.filter (fun j => j.val < k) := by
          ext j
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hj, hlt⟩
            have he : j.val ≠ k := fun eq => h ((Fin.ext (b := g) eq) ▸ hj)
            exact ⟨hj, by omega⟩
          · rintro ⟨hj, hlt⟩
            exact ⟨hj, by omega⟩
        rw [update]
        have hs : score k = score (k + 1) := free g h
        omega
  simpa using upto n le_rfl

lemma singleton_blocks_card {α : Type*} [DecidableEq α] (M : Finset α) (p0 p1 : α)
    (h0 : p0 ∈ M) (h1 : p1 ∈ M) (hne : p0 ≠ p1) (U : Finset (Finset α))
    (how : ∀ b, b ∈ U ↔ (∃ r ∈ M, b = {r}) ∧ p0 ∉ b ∧ p1 ∉ b) :
    U.card = M.card - 2 := by
  classical
  have same : U = ((M.erase p0).erase p1).image (fun x => ({x} : Finset α)) := by
    ext b
    rw [how, Finset.mem_image]
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, ha, hb⟩
      refine ⟨r, ?_, rfl⟩
      simp only [Finset.mem_singleton] at ha hb
      exact Finset.mem_erase.mpr ⟨Ne.symm hb, Finset.mem_erase.mpr ⟨Ne.symm ha, hr⟩⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hb, hr⟩ := Finset.mem_erase.mp hr
      obtain ⟨ha, hr⟩ := Finset.mem_erase.mp hr
      simpa using And.intro (show ∃ x ∈ M, ({r} : Finset α) = {x} from ⟨r, hr, rfl⟩)
        (And.intro (Ne.symm ha) (Ne.symm hb))
  have hp1 : p1 ∈ M.erase p0 := Finset.mem_erase.mpr ⟨hne.symm, h1⟩
  rw [same, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_erase_of_mem hp1, Finset.card_erase_of_mem h0]
  omega


noncomputable def component {α : Type*} [DecidableEq α] (M : Finset α)
    (C : Finset α → Prop) (x : α) : Finset α := by
  classical
  exact M.filter fun y => ∀ X, C X → (x ∈ X ↔ y ∈ X)

noncomputable def freeParts {α : Type*} [DecidableEq α] (M : Finset α)
    (C : Finset α → Prop) (D : Finset α) : Finset (Finset α) := by
  classical
  exact (M.image (component M C)).filter fun b => Disjoint b D

lemma component_mem {α : Type*} [DecidableEq α] {M : Finset α} {C : Finset α → Prop}
    {x y : α} : y ∈ component M C x ↔ y ∈ M ∧ ∀ X, C X → (x ∈ X ↔ y ∈ X) := by
  classical
  exact Finset.mem_filter

lemma component_self {α : Type*} [DecidableEq α] {M : Finset α} {C : Finset α → Prop}
    {x : α} (hx : x ∈ M) : x ∈ component M C x :=
  component_mem.mpr ⟨hx, fun _ _ => Iff.rfl⟩

lemma component_same {α : Type*} [DecidableEq α] {M : Finset α} {C : Finset α → Prop}
    {x y : α} (hy : y ∈ component M C x) : component M C y = component M C x := by
  ext z
  simp only [component_mem]
  have h := (component_mem.mp hy).2
  exact and_congr_right fun _ =>
    ⟨fun f X hX => (h X hX).trans (f X hX), fun f X hX => (h X hX).symm.trans (f X hX)⟩

lemma closed_union_parts {α : Type*} [DecidableEq α] (C : Finset α → Prop)
    (cup : ∀ X Y, C X → C Y → C (X ∪ Y)) (T : Finset (Finset α))
    (hne : T.Nonempty) (ht : ∀ b ∈ T, C b) : C (T.biUnion id) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp at hne
  | @insert s T hs ih =>
    rw [Finset.biUnion_insert]
    by_cases e : T.Nonempty
    · exact cup _ _ (ht s (Finset.mem_insert_self _ _))
        (ih e (fun b hb => ht b (Finset.mem_insert_of_mem hb)))
    · have none : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp e
      simpa [none] using ht s (Finset.mem_insert_self _ _)

lemma class_update {α : Type*} [DecidableEq α] (M A : Finset α)
    (C C' : Finset α → Prop) (hA : A ⊆ M)
    (hcls : ∀ x ∈ M, C (component M C x))
    (cup : ∀ X Y, C X → C Y → C (X ∪ Y))
    (rule : ∀ X, C' X ↔ C X ∧ ∀ a ∈ A, ∀ b ∈ A, (a ∈ X ↔ b ∈ X))
    (x : α) (hx : x ∈ M) :
    component M C' x =
      if component M C x ∈ A.image (component M C)
      then (A.image (component M C)).biUnion id else component M C x := by
  classical
  let T := A.image (component M C)
  let big := T.biUnion id
  have contains (a : α) (ha : a ∈ A) : a ∈ big :=
    Finset.mem_biUnion.mpr ⟨component M C a, Finset.mem_image_of_mem _ ha, component_self (hA ha)⟩
  by_cases hit : component M C x ∈ T
  · rw [ite_eq_left hit]
    change component M C' x = big
    have bigC : C big := closed_union_parts C cup T ⟨_, hit⟩ (by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact hcls a (hA ha))
    have bigC' : C' big := (rule _).mpr ⟨bigC, fun a ha b hb => iff_of_true (contains a ha) (contains b hb)⟩
    have xin : x ∈ big := Finset.mem_biUnion.mpr ⟨_, hit, component_self hx⟩
    ext y
    constructor
    · exact fun hy => ((component_mem.mp hy).2 big bigC').mp xin
    · intro hy
      obtain ⟨by', hby, hyy⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hby
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hit
      have hxx : x ∈ component M C a := hax.symm ▸ component_self hx
      refine component_mem.mpr ⟨(component_mem.mp hyy).1, fun X hX => ?_⟩
      obtain ⟨hOld, joined⟩ := (rule X).mp hX
      exact (((component_mem.mp hxx).2 X hOld).symm.trans (joined a ha b hb)).trans
        ((component_mem.mp hyy).2 X hOld)
  · rw [ite_eq_right hit]
    have untouched (a : α) (ha : a ∈ A) : a ∉ component M C x := by
      intro hm
      exact hit (Finset.mem_image.mpr ⟨a, ha, component_same hm⟩)
    have clsC' : C' (component M C x) := (rule _).mpr ⟨hcls x hx,
      fun a ha b hb => iff_of_false (untouched a ha) (untouched b hb)⟩
    ext y
    constructor
    · intro hy
      exact ((component_mem.mp hy).2 _ clsC').mp (component_self hx)
    · intro hy
      exact component_mem.mpr ⟨(component_mem.mp hy).1,
        fun X hX => (component_mem.mp hy).2 X ((rule X).mp hX).1⟩

lemma free_parts_update {α : Type*} [DecidableEq α] (M A D : Finset α)
    (C C' : Finset α → Prop) (hot : Prop) [Decidable hot] (hA : A ⊆ M)
    (hcls : ∀ x ∈ M, C (component M C x))
    (cup : ∀ X Y, C X → C Y → C (X ∪ Y))
    (rule : ∀ X, C' X ↔ C X ∧ ∀ a ∈ A, ∀ b ∈ A, (a ∈ X ↔ b ∈ X))
    (two : (A.image (component M C)).card ≤ 2)
    (hotOne : hot → ((A.image (component M C)).filter (fun b => Disjoint b D)).card ≤ 1) :
    let T := A.image (component M C)
    let F := T.filter (fun b => Disjoint b D)
    let before := (freeParts M C D).card
    let after := (freeParts M C' (D ∪ (if hot then A else ∅))).card
    after ≤ before ∧ before ≤ after + 1 ∧
      (F = ∅ ∨ (¬ hot ∧ T.card ≤ 1) → before = after) := by
  classical
  let T := A.image (component M C)
  let F := T.filter (fun b => Disjoint b D)
  let DD := D ∪ (if hot then A else ∅)
  let U := freeParts M C D
  let V := freeParts M C' DD
  let R := U \ T
  let J := T.biUnion id
  let keep : Prop := T.Nonempty ∧ ¬ hot ∧ T ⊆ F
  change V.card ≤ U.card ∧ U.card ≤ V.card + 1 ∧
    (F = ∅ ∨ (¬hot ∧ T.card ≤ 1) → U.card = V.card)
  have fsub : F ⊆ T := Finset.filter_subset _ _
  have old_mem {b : Finset α} : b ∈ U ↔ (∃ x ∈ M, component M C x = b) ∧ Disjoint b D :=
    Finset.mem_filter.trans (and_congr_left fun _ => Finset.mem_image)
  have new_mem {b : Finset α} : b ∈ V ↔ (∃ x ∈ M, component M C' x = b) ∧ Disjoint b DD :=
    Finset.mem_filter.trans (and_congr_left fun _ => Finset.mem_image)
  have f_as : U ∩ T = F := by
    ext b
    constructor
    · intro hb
      obtain ⟨hu, ht⟩ := Finset.mem_inter.mp hb
      exact Finset.mem_filter.mpr ⟨ht, (old_mem.mp hu).2⟩
    · intro hb
      obtain ⟨ht, hd⟩ := Finset.mem_filter.mp hb
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp ht
      exact Finset.mem_inter.mpr ⟨old_mem.mpr ⟨⟨a, hA ha, he⟩, hd⟩, ht⟩
  have old_count : R.card + F.card = U.card := by
    rw [← f_as]
    exact Finset.card_sdiff_add_card_inter U T
  have update (x : α) (hx : x ∈ M) :
      component M C' x = if component M C x ∈ T then J else component M C x :=
    class_update M A C C' hA hcls cup rule x hx
  have subs {b : Finset α} (hb : b ∈ T) : b ⊆ J :=
    fun _ hx => Finset.mem_biUnion.mpr ⟨b, hb, hx⟩
  have hasA {a : α} (ha : a ∈ A) : a ∈ J :=
    subs (Finset.mem_image_of_mem _ ha) (component_self (hA ha))
  have away (x : α) (miss : component M C x ∉ T) : Disjoint (component M C x) A :=
    Finset.disjoint_left.mpr fun a ha haA => miss (Finset.mem_image.mpr ⟨a, haA, component_same ha⟩)
  have keep_of (hn : T.Nonempty) (hd : Disjoint J DD) : keep := by
    obtain ⟨b, hb⟩ := hn
    obtain ⟨a, ha, _⟩ := Finset.mem_image.mp hb
    refine ⟨⟨b, hb⟩, ?_, fun b hb => Finset.mem_filter.mpr ⟨hb, ?_⟩⟩
    · intro hh
      exact Finset.disjoint_left.mp hd (hasA ha) (Finset.mem_union_right _ (by simpa [hh] using ha))
    · exact hd.mono (subs hb) Finset.subset_union_left
  have keep_disj (hk : keep) : Disjoint J DD := by
    obtain ⟨_, cold, hf⟩ := hk
    rw [show DD = D by simp [DD,cold]]
    apply Finset.disjoint_left.mpr
    intro a ha hd
    obtain ⟨b, hb, hba⟩ := Finset.mem_biUnion.mp ha
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp (hf hb)).2 hba hd
  have new_cases {b : Finset α} : b ∈ V ↔ b ∈ R ∨ (b = J ∧ keep) := by
    constructor
    · intro hb
      obtain ⟨⟨x, hx, rfl⟩, hd⟩ := new_mem.mp hb
      by_cases hit : component M C x ∈ T
      · rw [update x hx, ite_eq_left hit] at hd ⊢
        exact Or.inr ⟨rfl, keep_of ⟨_, hit⟩ hd⟩
      · rw [update x hx, ite_eq_right hit] at hd ⊢
        exact Or.inl (Finset.mem_sdiff.mpr ⟨old_mem.mpr
          ⟨⟨x,hx,rfl⟩, hd.mono_right Finset.subset_union_left⟩, hit⟩)
    · rintro (hr | ⟨rfl, hk⟩)
      · obtain ⟨hu, miss⟩ := Finset.mem_sdiff.mp hr
        obtain ⟨⟨x,hx,rfl⟩, hd⟩ := old_mem.mp hu
        apply new_mem.mpr
        refine ⟨⟨x, hx, (update x hx).trans (ite_eq_right miss)⟩, ?_⟩
        by_cases hh : hot
        · simpa [DD,hh,Finset.disjoint_union_right] using And.intro hd (away x miss)
        · simpa [DD,hh] using hd
      · obtain ⟨b, hb⟩ := hk.1
        obtain ⟨a, ha, _⟩ := Finset.mem_image.mp hb
        exact new_mem.mpr ⟨⟨a, hA ha, (update a (hA ha)).trans
          (ite_eq_left (Finset.mem_image_of_mem _ ha))⟩, keep_disj hk⟩
  have fcard : F.card ≤ T.card := Finset.card_le_card fsub
  change T.card ≤ 2 at two
  change hot → F.card ≤ 1 at hotOne
  by_cases hk : keep
  · have tn := hk.1
    have inclusive := hk.2.2
    have f_eq : F = T := Finset.Subset.antisymm fsub inclusive
    have fpos : 0 < F.card := f_eq ▸ Finset.card_pos.mpr tn
    have hnew : V = insert J R := by
      ext b
      rw [new_cases]
      simp only [hk, and_true, Finset.mem_insert, or_comm]
    have fresh : J ∉ R := by
      intro hj
      obtain ⟨hu, ht⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨⟨x, hx, hcomp⟩, _⟩ := old_mem.mp hu
      obtain ⟨b, hb⟩ := tn
      obtain ⟨a, ha, _⟩ := Finset.mem_image.mp hb
      have hax : a ∈ component M C x := hcomp ▸ hasA ha
      exact ht (Finset.mem_image.mpr ⟨a, ha, (component_same hax).trans hcomp⟩)
    rw [hnew, Finset.card_insert_of_notMem fresh]
    refine ⟨by omega, by omega, ?_⟩
    rintro (none | ⟨_, small⟩)
    · simp [none] at fpos
    · omega
  · have hnew : V = R := by
      ext b
      rw [new_cases]
      simp [hk]
    have fsmall : F.card ≤ 1 := by
      by_contra! h
      have htf : T ⊆ F := (Finset.eq_of_subset_of_card_le fsub (by omega)).symm.subset
      have tn : T.Nonempty := Finset.card_pos.mp (by omega)
      exact hk ⟨tn, fun hh => by have := hotOne hh; omega, htf⟩
    rw [hnew]
    refine ⟨by omega, by omega, ?_⟩
    rintro (none | ⟨cold, small⟩)
    · rw [none, Finset.card_empty, add_zero] at old_count
      omega
    · by_cases fpos : 0 < F.card
      · have htf : T ⊆ F := (Finset.eq_of_subset_of_card_le fsub (by omega)).symm.subset
        exact (hk ⟨Finset.card_pos.mp (by omega), cold, htf⟩).elim
      · omega

end PEqualNP.Outside.L_meta_1641

namespace PEqualNP.Outside.L_meta_1641
open PEqualNP.CircuitLowerBounds

variable {n m : ℕ}

def history (M : Finset (Fin n)) (K : Fin m → Prop) (S : Fin m → Fin n → Prop)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin m, i.val < k → K i → ∀ a ∈ M, ∀ b ∈ M, S i a → S i b → (a ∈ X ↔ b ∈ X)

noncomputable def region (M : Finset (Fin n)) (K : Fin m → Prop) (S : Fin m → Fin n → Prop)
    (i : Fin m) : Finset (Fin n) := by
  classical
  exact M.filter (fun p => K i ∧ S i p)

noncomputable def marks (M : Finset (Fin n)) (p0 p1 : Fin n)
    (K H : Fin m → Prop) (S : Fin m → Fin n → Prop) (k : ℕ) : Finset (Fin n) := by
  classical
  exact M.filter (fun p => p = p0 ∨ p = p1 ∨ ∃ i : Fin m, i.val < k ∧ K i ∧ H i ∧ S i p)

lemma history_comp (M : Finset (Fin n)) (K : Fin m → Prop) (S : Fin m → Fin n → Prop)
    (k : ℕ) (x : Fin n) :
    history M K S k (component M (history M K S k) x) := by
  classical
  intro i hi hK a ha b hb hsa hsb
  have h : ∀ X, history M K S k X → (a ∈ X ↔ b ∈ X) :=
    fun X hX => hX i hi hK a ha b hb hsa hsb
  simp only [component, Finset.mem_filter, ha, hb, true_and]
  exact ⟨fun hx X hX => (hx X hX).trans (h X hX),
    fun hx X hX => (hx X hX).trans (h X hX).symm⟩

lemma history_union (M : Finset (Fin n)) (K : Fin m → Prop) (S : Fin m → Fin n → Prop)
    (k : ℕ) {X Y : Finset (Fin n)} (hX : history M K S k X) (hY : history M K S k Y) :
    history M K S k (X ∪ Y) := by
  intro i hi hK a ha b hb hsa hsb
  simp only [Finset.mem_union]
  exact or_congr (hX i hi hK a ha b hb hsa hsb) (hY i hi hK a ha b hb hsa hsb)

lemma history_update (M : Finset (Fin n)) (K : Fin m → Prop) (S : Fin m → Fin n → Prop)
    (i : Fin m) (X : Finset (Fin n)) :
    history M K S (i.val+1) X ↔ history M K S i.val X ∧
      ∀ a ∈ region M K S i, ∀ b ∈ region M K S i, (a ∈ X ↔ b ∈ X) := by
  classical
  constructor
  · intro h
    refine ⟨fun j hj => h j (by omega), ?_⟩
    intro a ha b hb
    simp only [region, Finset.mem_filter] at ha hb
    exact h i (by omega) ha.2.1 a ha.1 b hb.1 ha.2.2 hb.2.2
  · rintro ⟨h, hi⟩ j hj hK a ha b hb hsa hsb
    by_cases hji : j.val < i.val
    · exact h j hji hK a ha b hb hsa hsb
    · have e : j = i := Fin.ext (by omega)
      subst j
      exact hi a (by simp [region, ha, hK, hsa]) b (by simp [region, hb, hK, hsb])

lemma marks_update (M : Finset (Fin n)) (p0 p1 : Fin n)
    (K H : Fin m → Prop) (S : Fin m → Fin n → Prop) (i : Fin m) [Decidable (H i)] :
    marks M p0 p1 K H S (i.val + 1) =
      marks M p0 p1 K H S i.val ∪ (if H i then region M K S i else ∅) := by
  classical
  ext a
  have split : (∃ j : Fin m, j.val < i.val+1 ∧ K j ∧ H j ∧ S j a) ↔
      (∃ j : Fin m, j.val < i.val ∧ K j ∧ H j ∧ S j a) ∨ K i ∧ H i ∧ S i a := by
    constructor
    · rintro ⟨j,hj,hK,hH,hS⟩
      by_cases e : j.val < i.val
      · exact Or.inl ⟨j,e,hK,hH,hS⟩
      · have hji : j=i := Fin.ext (by omega)
        exact Or.inr (hji ▸ And.intro hK (And.intro hH hS))
    · rintro (⟨j,hj,hK,hH,hS⟩|hh)
      · exact ⟨j,by omega,hK,hH,hS⟩
      · exact ⟨i,by omega,hh⟩
  by_cases h : H i <;> simp only [marks,region,Finset.mem_filter,Finset.mem_union,split,h,
    ite_true,ite_false,Finset.notMem_empty,and_false,false_and,true_and,or_false]
  simp only [and_or_left, or_assoc]

lemma free_parts_desc (M : Finset (Fin n)) (p0 p1 : Fin n)
    (K H : Fin m → Prop) (S : Fin m → Fin n → Prop) (k : ℕ) (b : Finset (Fin n)) :
    b ∈ freeParts M (history M K S k) (marks M p0 p1 K H S k) ↔
    (∃ r ∈ M, ∀ a, a ∈ b ↔ a ∈ M ∧ ∀ X, history M K S k X → (r ∈ X ↔ a ∈ X)) ∧
    p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin m, i.val < k → K i → H i → ∀ s ∈ b, ¬ S i s := by
  classical
  simp only [freeParts, Finset.mem_filter, Finset.mem_image, Finset.disjoint_left]
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hd⟩
    have desc (a) : a ∈ component M (history M K S k) r ↔ _ := component_mem
    refine ⟨⟨r, hr, desc⟩, ?_, ?_, ?_⟩
    · intro hx
      exact hd hx (by simp [marks,(desc _).mp hx |>.1])
    · intro hx
      exact hd hx (by simp [marks,(desc _).mp hx |>.1])
    · intro i hi hK hH s hs hS
      exact hd hs (Finset.mem_filter.mpr ⟨((desc _).mp hs).1, Or.inr (Or.inr ⟨i,hi,hK,hH,hS⟩)⟩)
  · rintro ⟨⟨r, hr, desc⟩, h0, h1, hi⟩
    refine ⟨⟨r,hr, Finset.ext (fun a => (show a ∈ component M (history M K S k) r ↔ _ from
      component_mem).trans (desc a).symm)⟩, ?_⟩
    intro a ha hd
    rcases (Finset.mem_filter.mp hd).2 with h|h|⟨i,hlt,hK,hH,hS⟩
    · exact h0 (h ▸ ha)
    · exact h1 (h ▸ ha)
    · exact hi i hlt hK hH a ha hS

lemma touched_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset ℕ) (f : α → β) (P : ℕ → α → Prop)
    (cover : ∀ p ∈ A, ∃ e ∈ B, P e p)
    (one : ∀ e ∈ B, ∀ p ∈ A, ∀ q ∈ A, P e p → P e q → f p = f q) :
    (A.image f).card ≤ B.card := by
  classical
  let d (e : ℕ) : Option β := if h : ∃ p ∈ A, P e p then some (f h.choose) else none
  have hmap : (A.image f).image some ⊆ B.image d := by
    intro z hz
    obtain ⟨_, hf, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨e, he, hep⟩ := cover p hp
    refine Finset.mem_image.mpr ⟨e,he,?_⟩
    have h : ∃ p ∈ A, P e p := ⟨p,hp,hep⟩
    simp only [d,dite_eq_left h,Option.some.injEq]
    exact one e he _ h.choose_spec.1 p hp h.choose_spec.2 hep
  have := (Finset.card_le_card hmap).trans Finset.card_image_le
  simpa only [Finset.card_image_of_injective _ (Option.some_injective β)] using this

end PEqualNP.Outside.L_meta_1641

namespace PEqualNP.Outside.L_meta_1641
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}

lemma child_history (gs : List Gate) (M : Finset (Fin n)) (p0 p1 : Fin n)
    (earlier : ∀ i : Fin gs.length, ∀ e ∈ (gs.get i).inputs, e < n + i.val)
    (j : Fin gs.length) (hj : cleanG gs M j) {e : ℕ} (he : e ∈ (gs.get j).inputs)
    {p : Fin n} (hp : p ∈ M) (hsp : OrTop n gs e p) :
    (∀ q ∈ M, OrTop n gs e q →
      component M (history M (cleanG gs M) (topG gs) j.val) p =
      component M (history M (cleanG gs M) (topG gs) j.val) q) ∧
    (hotW gs p0 p1 e → p ∈ marks M p0 p1 (cleanG gs M)
      (fun i => hotW gs p0 p1 (n+i.val)) (topG gs) j.val) := by
  classical
  have hel := earlier j e he
  have hef := wire_or_false_child gs j hj.1 (offLine M) he hel hj.2
  by_cases hr : e < n
  · let r : Fin n := ⟨e,hr⟩
    have hsp' : r=p := (orTop_raw gs r p).mp hsp
    subst p
    constructor
    · intro q _ hsq
      rw [(orTop_raw gs r q).mp hsq]
    · intro hh
      change wireValue gs r (pointBit p0) = true ∨ wireValue gs r (pointBit p1) = true at hh
      simp only [wire_input, pointBit, decide_eq_true_eq] at hh
      simp only [marks, Finset.mem_filter]
      exact ⟨hp,hh.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  · let i : Fin gs.length := ⟨e-n, by have := j.isLt; omega⟩
    have hi : i.val < j.val := by dsimp [i]; omega
    have eq : n+i.val=e := by dsimp [i]; omega
    have hsp' : topG gs i p := by simpa only [topG,eq] using hsp
    have hg : cleanG gs M i := ⟨((orTop_gate gs i p).mp hsp').1, eq ▸ hef⟩
    constructor
    · intro q hq hs
      have hs' : topG gs i q := by simpa only [topG,eq] using hs
      exact (component_same (component_mem.mpr ⟨hq, fun _ hX =>
        hX i hi hg p hp q hq hsp' hs'⟩)).symm
    · intro hh
      simp only [marks,Finset.mem_filter]
      exact ⟨hp, Or.inr (Or.inr ⟨i,hi,hg,by simpa only [eq] using hh,hsp'⟩)⟩

lemma step_sizes (gs : List Gate) (M : Finset (Fin n)) (p0 p1 : Fin n)
    (hg : good ⟨gs,0⟩)
    (earlier : ∀ i : Fin gs.length, ∀ e ∈ (gs.get i).inputs, e < n+i.val)
    (j : Fin gs.length) :
    let K := cleanG gs M
    let H := fun i : Fin gs.length => hotW gs p0 p1 (n+i.val)
    let S := @topG n gs
    let A := region M K S j
    let c := component M (history M K S j.val)
    let T := A.image c
    let D := marks M p0 p1 K H S j.val
    let F := T.filter (fun b => Disjoint b D)
    T.card ≤ 2 ∧ (H j → F.card ≤ 1) ∧
      ((∀ e ∈ (gs.get j).inputs, hotW gs p0 p1 e) → F=∅) := by
  classical
  let K := cleanG gs M
  let H := fun i : Fin gs.length => hotW gs p0 p1 (n+i.val)
  let S := @topG n gs
  let A := region M K S j
  let c := component M (history M K S j.val)
  let T := A.image c
  let D := marks M p0 p1 K H S j.val
  let F := T.filter (fun b => Disjoint b D)
  change T.card ≤ 2 ∧ (H j → F.card ≤ 1) ∧ _
  let B := (gs.get j).inputs.toFinset
  let B' := B.filter (fun e => ¬ hotW gs p0 p1 e)
  let A' := A.filter (fun p => Disjoint (c p) D)
  have ha (p : Fin n) : p ∈ A ↔ p ∈ M ∧ K j ∧ S j p := by simp [A,region]
  have cover (p) (hp : p ∈ A) : ∃ e ∈ B, OrTop n gs e p := by
    obtain ⟨e,he,hsp⟩ := ((orTop_gate gs j p).mp ((ha p).mp hp).2.2).2
    exact ⟨e,List.mem_toFinset.mpr he,hsp⟩
  have one (e) (he : e ∈ B) (p) (hp : p ∈ A) (q) (hq : q ∈ A) (hsp : OrTop n gs e p)
      (hsq : OrTop n gs e q) : c p=c q := by
    obtain ⟨hpM,hK,_⟩ := (ha p).mp hp
    exact (child_history gs M p0 p1 earlier j hK (List.mem_toFinset.mp he) hpM hsp).1
      q ((ha q).mp hq).1 hsq
  have hB : B.card ≤ 2 := (List.toFinset_card_le _).trans
    ((hg _ (List.get_mem gs j)).2)
  refine ⟨(touched_card A B c (fun e p => OrTop n gs e p) cover one).trans hB, ?_⟩
  have sub : F ⊆ A'.image c := by
    intro b hb
    obtain ⟨ht,hd⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hd⟩,rfl⟩
  have cov' (p) (hp : p ∈ A') : ∃ e ∈ B', OrTop n gs e p := by
    obtain ⟨ha',hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨e,he,hs⟩ := cover p ha'
    obtain ⟨hpM,hK,_⟩ := (ha p).mp ha'
    refine ⟨e, Finset.mem_filter.mpr ⟨he,?_⟩,hs⟩
    intro hh
    have hD := (child_history gs M p0 p1 earlier j hK (List.mem_toFinset.mp he) hpM hs).2 hh
    exact Finset.disjoint_left.mp hd (component_self hpM) hD
  have bound : F.card ≤ B'.card := (Finset.card_le_card sub).trans
    (touched_card A' B' c (fun e p => OrTop n gs e p) cov' (fun e he p hp q hq =>
      one e (Finset.mem_filter.mp he).1 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1))
  constructor
  · intro hh
    by_cases hK : K j
    · have hotchild : ∃ e ∈ B, hotW gs p0 p1 e := by
        rcases hh with hh|hh
        · obtain ⟨e,he,_,hhot⟩ := (wire_or gs j hK.1 (pointBit p0)).mp hh
          exact ⟨e,List.mem_toFinset.mpr he,Or.inl hhot⟩
        · obtain ⟨e,he,_,hhot⟩ := (wire_or gs j hK.1 (pointBit p1)).mp hh
          exact ⟨e,List.mem_toFinset.mpr he,Or.inr hhot⟩
      obtain ⟨e,he,hh'⟩ := hotchild
      have hlt : B'.card < B.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun eq =>
          (Finset.mem_filter.mp (eq ▸ he : e ∈ B')).2 hh'⟩)
      omega
    · have eA : A = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => hK ((ha p).mp hp).2.1)
      simp [F,T,eA]
  · intro hall
    have emp : B'=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e he =>
      (Finset.mem_filter.mp he).2 (hall e (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)))
    change F=∅
    simpa only [emp, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] using bound

end PEqualNP.Outside.L_meta_1641

namespace PEqualNP.Outside.L_meta_1641

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma step_free (gs : List Gate) (L : Fin n → Finset (Fin n)) (i0 p0 p1 : Fin n)
    (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0) (hg : good ⟨gs,0⟩)
    (earlier : ∀ i : Fin gs.length, ∀ e ∈ (gs.get i).inputs, e < n+i.val)
    (hpair : ∀ i j : Fin n, i ≠ j → (L i ∩ L j).card=1) (j : Fin gs.length) :
    let M := L i0
    let K := cleanG gs M
    let H := fun i : Fin gs.length => hotW gs p0 p1 (n+i.val)
    let S := @topG n gs
    let A := region M K S j
    let c := component M (history M K S j.val)
    let T := A.image c
    let D := marks M p0 p1 K H S j.val
    let F := T.filter (fun b => Disjoint b D)
    ((∀ e ∈ (gs.get j).inputs, hotW gs p0 p1 e) → F = ∅) →
    ¬ ((K j ∧ ∀ t, t ≠ i0 → wireValue gs (n+j.val) (offLine (L t))=true) ∧
        ¬ ∀ e ∈ (gs.get j).inputs, hotW gs p0 p1 e) →
    F = ∅ ∨ (¬ H j ∧ T.card ≤ 1) := by
  classical
  let M := L i0
  let K := cleanG gs M
  let H := fun i : Fin gs.length => hotW gs p0 p1 (n+i.val)
  let S := @topG n gs
  let A := region M K S j
  let c := component M (history M K S j.val)
  let T := A.image c
  let D := marks M p0 p1 K H S j.val
  let F := T.filter (fun b => Disjoint b D)
  change ((∀ e ∈ (gs.get j).inputs, hotW gs p0 p1 e) → F = ∅) → _ →
    F = ∅ ∨ (¬ H j ∧ T.card ≤ 1)
  intro hall hnot
  by_cases hF : F = ∅
  · exact Or.inl hF
  right
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hF
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hb).1
  have hregion (r : Fin n) (hr : r ∈ A) : r ∈ M ∧ K j ∧ S j r := by
    simpa only [A, region, Finset.mem_filter] using hr
  have hj := (hregion a ha).2.1
  have hnoAll : ¬ ∀ e ∈ (gs.get j).inputs, hotW gs p0 p1 e := fun h => hF (hall h)
  have hfalse : ∃ t, t ≠ i0 ∧ wireValue gs (n+j.val) (offLine (L t)) = false := by
    by_contra no
    apply hnot
    refine ⟨⟨hj, fun t ht => ?_⟩, hnoAll⟩
    cases ev : wireValue gs (n+j.val) (offLine (L t)) with
    | true => rfl
    | false => exact (no ⟨t, ht, ev⟩).elim
  obtain ⟨t, ht, hf⟩ := hfalse
  have htrue (r : Fin n) (hr : r ∈ A) : wireValue gs (n+j.val) (pointBit r) = true :=
    orTop_singleton gs earlier (hregion r hr).2.2
  have unique {r s : Fin n} (hr : r ∈ M) (hs : s ∈ M)
      (htr : wireValue gs (n+j.val) (pointBit r) = true)
      (hts : wireValue gs (n+j.val) (pointBit s) = true) : r = s :=
    subsingleton_of_off_false gs hg M (L t) (hpair i0 t ht.symm) (n+j.val) hf hr hs htr hts
  have hD (p : Fin n) (hp : p ∈ M) (hh : p = p0 ∨ p = p1) : p ∈ D := by
    simp only [D, marks, Finset.mem_filter]
    exact ⟨hp, hh.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  have hdis : Disjoint (c a) D := he.symm ▸ (Finset.mem_filter.mp hb).2
  constructor
  · intro hot
    have haM := (hregion a ha).1
    have has : a ∈ c a := component_self haM
    rcases hot with hot0 | hot1
    · have ea := unique haM h0 (htrue a ha) hot0
      exact Finset.disjoint_left.mp hdis (ea ▸ has) (hD p0 h0 (Or.inl rfl))
    · have ea := unique haM h1 (htrue a ha) hot1
      exact Finset.disjoint_left.mp hdis (ea ▸ has) (hD p1 h1 (Or.inr rfl))
  · apply Finset.card_le_one.mpr
    intro b₁ hb₁ b₂ hb₂
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb₁
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb₂
    exact congrArg c (unique (hregion r hr).1 (hregion s hs).1 (htrue r hr) (htrue s hs))

end PEqualNP.Outside.L_meta_1641

namespace PEqualNP.Outside.L_meta_1641
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}

lemma step_circuit (gs : List Gate) (L : Fin n → Finset (Fin n)) (i0 p0 p1 : Fin n)
    (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0) (hg : good ⟨gs,0⟩)
    (earlier : ∀ i : Fin gs.length, ∀ e ∈ (gs.get i).inputs, e < n+i.val)
    (hpair : ∀ i j : Fin n, i ≠ j → (L i ∩ L j).card=1) (j : Fin gs.length) :
    let M := L i0
    let K := cleanG gs M
    let H := fun i : Fin gs.length => hotW gs p0 p1 (n+i.val)
    let S := @topG n gs
    let U := fun k => freeParts M (history M K S k) (marks M p0 p1 K H S k)
    (U (j.val+1)).card ≤ (U j.val).card ∧ (U j.val).card ≤ (U (j.val+1)).card + 1 ∧
      (¬ ((K j ∧ ∀ t, t ≠ i0 → wireValue gs (n+j.val) (offLine (L t))=true) ∧
        ¬ ∀ e ∈ (gs.get j).inputs, hotW gs p0 p1 e) → (U j.val).card=(U (j.val+1)).card) := by
  classical
  let M := L i0
  let K := cleanG gs M
  let H := fun i : Fin gs.length => hotW gs p0 p1 (n+i.val)
  let S := @topG n gs
  let A := region M K S j
  let C := history M K S j.val
  let C' := history M K S (j.val+1)
  let D := marks M p0 p1 K H S j.val
  obtain ⟨two,hotOne,hall⟩ := step_sizes gs M p0 p1 hg earlier j
  have hA : A ⊆ M := by
    intro a ha
    simp only [A,region,Finset.mem_filter] at ha
    exact ha.1
  have h := free_parts_update M A D C C' (H j) hA (fun x _ => history_comp M K S j.val x)
    (fun _ _ hx hy => history_union M K S j.val hx hy) (history_update M K S j)
    two hotOne
  dsimp only at h ⊢
  rw [marks_update M p0 p1 K H S j]
  refine ⟨h.1, h.2.1, fun hnot => h.2.2 ?_⟩
  exact step_free gs L i0 p0 p1 h0 h1 hg earlier hpair j hall hnot

end PEqualNP.Outside.L_meta_1641

open PEqualNP.Outside.L_meta_1641

theorem PEqualNP.Outside.L_meta_1641 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ UB : ℕ → Finset (Finset (Fin N)),
    (∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔ ((∃ r ∈ L i0, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ L i0 ∧ ∀ X : Finset (Fin N), (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
          ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ∧
        p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) → ∀ s ∈ b, ¬ St (N + (i : ℕ)) s)) →
    ∀ Xs : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ Xs ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true))) →
      (∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧ (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = q - 1 ∧ q - 1 ≤ Xs.card + (UB gates.length).card := by
  classical
  intro q N L i0 p0 p1 _ _ hcard hpair _ hne h0 h1 gs hg _ earlier ev hev
    o0 _ _ _ _ St hSt UB hUB Xs hXs
  have evEq : ev = wireValue gs := funext fun w => funext fun x => hev w x
  subst ev
  have stEq : St = OrTop N gs := funext fun w => funext fun p => propext (hSt w p)
  subst St
  let M := L i0
  let K := cleanG gs M
  let H := fun i : Fin gs.length => hotW gs p0 p1 (N+i.val)
  let S := @topG N gs
  let U := fun k => freeParts M (history M K S k) (marks M p0 p1 K H S k)
  have agree (k : ℕ) : UB k = U k := by
    ext b
    rw [hUB k b]
    change _ ↔ b ∈ freeParts M (history M K S k) (marks M p0 p1 K H S k)
    rw [free_parts_desc]
    simp only [M, K, H, S, history, cleanG, topG, hotW, and_imp]
  have step (j : Fin gs.length) :
      (UB (j.val + 1)).card ≤ (UB j.val).card ∧
      (UB j.val).card ≤ (UB (j.val + 1)).card + 1 ∧
      (j ∉ Xs → (UB j.val).card = (UB (j.val + 1)).card) := by
    rw [agree (j.val + 1), agree j.val]
    have t := step_circuit gs L i0 p0 p1 h0 h1 hg earlier hpair j
    refine ⟨t.1, t.2.1, fun hj => t.2.2 ?_⟩
    intro h
    apply hj
    apply (hXs j).mpr
    simpa only [cleanG, hotW, offLine, pointBit, and_assoc] using h
  have zeroCount : (UB 0).card = (L i0).card - 2 := by
    apply singleton_blocks_card (L i0) p0 p1 h0 h1 hne
    intro b
    rw [hUB 0 b]
    simp only [Nat.not_lt_zero, false_implies, implies_true, true_implies, and_true]
    apply and_congr_left
    intro _
    constructor
    · rintro ⟨r, hr, desc⟩
      refine ⟨r, hr, Finset.ext (fun y => ?_)⟩
      rw [desc]
      constructor
      · rintro ⟨_, same⟩
        exact (same {r}).mp (Finset.mem_singleton_self _)
      · intro hy
        have yr : y = r := Finset.mem_singleton.mp hy
        subst y
        exact ⟨hr, fun _ => Iff.rfl⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r, hr, fun y => ?_⟩
      constructor
      · intro hy
        have yr : y = r := Finset.mem_singleton.mp hy
        subst y
        exact ⟨hr, fun _ => Iff.rfl⟩
      · rintro ⟨_, same⟩
        exact (same {r}).mp (Finset.mem_singleton_self _)
  have z : (UB 0).card = q - 1 := by
    rw [zeroCount, hcard i0]
    omega
  refine ⟨step, z, ?_⟩
  rw [← z]
  exact telescope_unanchored (fun k => (UB k).card) Xs
    (fun j => (step j).2.1) (fun j => (step j).2.2)
