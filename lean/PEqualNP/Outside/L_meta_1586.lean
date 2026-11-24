import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1586

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

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

def OrClosed (n : ℕ) (gs : List Gate) (S : Set ℕ) : Prop :=
  ∀ i : Fin gs.length, n + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
    ∀ a ∈ (gs.get i).inputs, a ∈ S

def OrTop (n : ℕ) (gs : List Gate) (u w : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → OrClosed n gs S → w ∈ S

lemma top_child {n u : ℕ} {gs : List Gate} {i : Fin gs.length}
    (parent : OrTop n gs u (n + (i : ℕ))) (hop : (gs.get i).op = GateOp.or)
    {a : ℕ} (ha : a ∈ (gs.get i).inputs) : OrTop n gs u a :=
  fun S hu closed => closed i (parent S hu closed) hop a ha

lemma false_top {n u : ℕ} {gs : List Gate} (x : Fin n → Bool)
    (earlier : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < n + (i : ℕ))
    (hu : value ⟨gs, 0⟩ x u = false) (w : ℕ) (hw : OrTop n gs u w) :
    value ⟨gs, 0⟩ x w = false := by
  apply hw {v | value ⟨gs, 0⟩ x v = false} hu
  intro i hi hop a ha
  change value ⟨gs, 0⟩ x (n + (i : ℕ)) = false at hi
  change value ⟨gs, 0⟩ x a = false
  by_contra h
  have hon := (or_value ⟨gs, 0⟩ i i.isLt hop x).mpr
    ⟨a, ha, earlier i a ha, by simpa using h⟩
  rw [hi] at hon
  exact Bool.noConfusion hon

lemma true_frontier {n u : ℕ} {gs : List Gate} (x : Fin n → Bool) (r : Fin n)
    (ops : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or)
    (inputs : ∀ p : Fin n, OrTop n gs u p → x p = true → p = r)
    (w : ℕ) (hw : OrTop n gs u w) (hon : value ⟨gs, 0⟩ x w = true) :
    OrTop n gs u r ∨ ∃ a : ℕ, OrTop n gs u a ∧
      (∃ i : Fin gs.length, a = n + (i : ℕ) ∧ (gs.get i).op = GateOp.and) ∧
      value ⟨gs, 0⟩ x a = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w < n
    · let p : Fin n := ⟨w, raw⟩
      have hp : x p = true := (input_value ⟨gs, 0⟩ x p).symm.trans hon
      have eq := inputs p hw hp
      left
      rw [← eq]
      exact hw
    by_cases valid : w < n + gs.length
    · let i : Fin gs.length := ⟨w - n, by omega⟩
      have eq : w = n + (i : ℕ) := by change w = n + (w - n); omega
      have onGate : value ⟨gs, 0⟩ x (n + (i : ℕ)) = true := eq ▸ hon
      rcases ops i with hand | hor
      · exact Or.inr ⟨w, hw, ⟨i, eq, hand⟩, hon⟩
      · obtain ⟨a, ha, hlt, ht⟩ := (or_value ⟨gs, 0⟩ i i.isLt hor x).mp onGate
        have topGate : OrTop n gs u (n + (i : ℕ)) := eq ▸ hw
        exact ih a (hlt.trans_le eq.ge) (top_child topGate hor ha) ht
    · have off := missing_value (⟨gs, 0⟩ : Circuit) x w
          (by change n + gs.length ≤ w; omega)
      rw [off] at hon
      exact Bool.noConfusion hon

end PEqualNP.Outside.L_meta_1586

open PEqualNP.Outside.L_meta_1586

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gs u hg hw hu
  let outside := fun p : Fin N => decide (p ∉ L i0)
  have falses := false_top (gs := gs) (u := u) outside (fun i => (hw i).2) hu
  have in_line (p : Fin N) (hp : OrTop N gs u p) : p ∈ L i0 := by
    have h := (input_value (⟨gs, 0⟩ : Circuit) outside p).symm.trans (falses p hp)
    simpa [outside] using h
  refine ⟨falses, in_line, ?_, ?_⟩
  · intro r _ htrue
    let x := fun v : Fin N => decide (v ∉ L i0 ∨ v = r)
    apply true_frontier (gs := gs) (u := u) x r (fun i => (hg _ (List.get_mem gs i)).1) ?_ u
      (fun S huS _ => huS) htrue
    intro p hp h
    have hx : p ∉ L i0 ∨ p = r := of_decide_eq_true h
    exact hx.resolve_left (not_not_intro (in_line p hp))
  · intro a c hop _ hc _ r _ ht
    exact ((and_value (⟨gs, 0⟩ : Circuit) a a.isLt hop
      (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))).mp ht c hc).2
