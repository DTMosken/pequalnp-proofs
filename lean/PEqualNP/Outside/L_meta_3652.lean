import PEqualNP.Defs
import Mathlib.Data.Finset.Max

-- Circuit and cone recurrences adapted from L-meta-2067 by willakone, PR 4293.
-- Word semantics adapted from L-meta-2466 by m-simonelli, PR 4878,
-- building on L-meta-1942 by npollock14, PR 4373.
-- The core extraction and maximal-core extension below prove L-meta-3652.


namespace PEqualNP.Outside.L_meta_3652.Structure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

-- Evaluation and strict-cone recurrences adapted from L_meta_2067.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

lemma ao_aob {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : AOB n C := by
  intro j hj
  exact ⟨hAO.1 _ (gateAt_mem C j hj), hAO.2.1 j hj⟩

lemma operand_position {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j w : ℕ} (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) :
    ∃ b : Fin 2, opnd C j b = w := by
  obtain ⟨b, hb, he⟩ := List.mem_iff_getElem.mp hw
  have hlen := hAO.2.2 _ (gateAt_mem C j hj)
  have hb2 : b < 2 := by omega
  refine ⟨⟨b, hb2⟩, ?_⟩
  simpa only [opnd, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hb, Option.getD_some] using he

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

-- An implicant cannot feed an AND under the no-read assumption. A live OR
-- reading one must itself be an implicant at a lift fixed point.
theorem imp_reader (hAO : IsAO2 n C) (hfixed : IsLiftFixedPoint G C)
    (hlive : ∀ k < C.gates.length, InOutputCone n C k)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true))
    {i j : ℕ} (hj : j < C.gates.length) (hread : n + i ∈ (gateAt C j).inputs)
    (hi : IsImpGate G C i) :
    IsImpGate G C j ∧
      ∀ x : Fin n → Bool, gateVal n C i x = true → gateVal n C j x = true := by
  have hOR : (gateAt C j).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem C j hj) with hAND | hOR
    · exact False.elim (hno j hj hAND (n + i) hread (by
        simpa only [BelowF, Circuit.eval, Circuit.wires, gateVal] using hi.1))
    · exact hOR
  have hpass : ∀ x : Fin n → Bool,
      gateVal n C i x = true → gateVal n C j x = true := by
    intro x hx
    change wv n C x (n + j) = true
    rw [wv_rec n C x (ao_aob hAO) j hj, hOR]
    simp only [GateOp.eval, List.any_map]
    exact List.any_eq_true.mpr ⟨n + i, hread, hx⟩
  have hbelow : BelowF G C j := by
    by_contra hn
    obtain ⟨b, hb⟩ := operand_position hAO hj hread
    apply hfixed
    refine ⟨j, hj, b, hlive j hj, hOR, hn, ?_⟩
    rw [IsImpWire, hb]
    simpa only [IsImpGate, BelowF, wval, gateVal] using hi
  obtain ⟨x, hx⟩ := hi.2
  exact ⟨⟨hbelow, x, hpass x hx⟩, hpass⟩

theorem imp_cone (hAO : IsAO2 n C) (hfixed : IsLiftFixedPoint G C)
    (hlive : ∀ k < C.gates.length, InOutputCone n C k)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true))
    {i : ℕ} (hi : IsImpGate G C i) :
    ∀ j, InCone n C i j → IsImpGate G C j ∧
      ∀ x : Fin n → Bool, gateVal n C i x = true → gateVal n C j x = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hcone
    obtain ⟨hj, k, hk, hread, hik | hik⟩ := (inCone_iff n C i j).mp hcone
    · subst k
      exact imp_reader hAO hfixed hlive hno hj hread hi
    · have hkimp := ih k hk hik
      have hjimp := imp_reader hAO hfixed hlive hno hj hread hkimp.1
      exact ⟨hjimp.1, fun x hx => hjimp.2 x (hkimp.2 x hx)⟩

theorem maximal_core_accepts (hAO : IsAO2 n C) (hfixed : IsLiftFixedPoint G C)
    (hlive : ∀ k < C.gates.length, InOutputCone n C k)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true))
    {j : ℕ} (hj : IsCore G C j) {e : Sym2 (Fin n)} (he : e ∈ gammaE G C j) :
    ∃ k ∈ maximalCores G C, e ∈ gammaE G C k := by
  classical
  let S := (Finset.range C.gates.length).filter
    (fun k => IsCore G C k ∧ e ∈ gammaE G C k)
  have hS : S.Nonempty := by
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj.1, hj, he⟩
  let k := S.max' hS
  have hkS : k ∈ S := Finset.max'_mem S hS
  obtain ⟨hklen, hkcore, hke⟩ :=
    (show k < C.gates.length ∧ IsCore G C k ∧ e ∈ gammaE G C k from by
      simpa only [S, Finset.mem_filter, Finset.mem_range] using hkS)
  have hmax : IsMaximalCore G C k := by
    refine ⟨hkcore, ?_⟩
    intro z hz hzcore hcone
    have hpass := (imp_cone hAO hfixed hlive hno hkcore.2.1 z hcone).2
    have hze : e ∈ gammaE G C z := by
      obtain ⟨hGe, u, v, huv, hv⟩ := Finset.mem_filter.mp hke
      exact Finset.mem_filter.mpr ⟨hGe, u, v, huv, hpass (pairInput u v) hv⟩
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨hz, hzcore, hze⟩
    have hle : z ≤ k := Finset.le_max' S z hzS
    have hlt := (inCone_lt n C k z hcone).1
    omega
  refine ⟨k, ?_, hke⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklen, hmax⟩

end PEqualNP.Outside.L_meta_3652.Structure

namespace PEqualNP.Outside.L_meta_3652.ReadWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit

def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit

section ReadWitness

-- Decode capped multiplicities into actual words of input leaves.

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

lemma mem_andStep_one (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 1 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 1 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 2

lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

lemma encode_append (S t u : List ℕ) :
    capAdd 1 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 1) [S.map fun _ => 0]
  | _ => []

def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 1).getD w [])

lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 1))).getD w [] :=
  rfl

lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 1)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (1 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 1)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 1 (andStep 1 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_one _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_one _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 1 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 1 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 2 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


section SingleLine

open PEqualNP.ReadK

def markedOp (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | .or => (ins.any (·.1), ins.any (·.2))
  | .and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def markedStart {N : ℕ} (p l : Fin N) : List (Bool × Bool) :=
  (((List.range (N + N)).map (fun i => i == p.val || i == N + l.val)).zipIdx).map
    (fun (b,i) => if decide (N ≤ i) then (false,b) else (b,false))

def markedValue {N : ℕ} (C : Circuit) (p l : Fin N) (w : ℕ) : Bool × Bool :=
  (evalFrom (false,false) markedOp C.gates (markedStart p l)).getD w (false,false)

lemma markedStart_length {N : ℕ} (p l : Fin N) :
    (markedStart p l).length = N + N := by simp [markedStart]

lemma markedInput {N : ℕ} (C : Circuit) (p l : Fin N) {w : ℕ}
    (hw : w < N + N) :
    markedValue C p l w =
      if w < N then (decide (w = p.val), false)
      else (false, decide (w = N + l.val)) := by
  have hw' : w < (markedStart p l).length := by simpa [markedStart_length] using hw
  unfold markedValue
  rw [evalFrom_input _ _ _ _ _ hw', List.getD_eq_getElem?_getD]
  simp only [markedStart, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_range hw,
    Option.map_some, Nat.zero_add, Option.getD_some]
  by_cases hl : w < N
  · have hn : w ≠ N + l.val := by omega
    have hnl : ¬ N ≤ w := by omega
    simp [hl, hnl, hn, Bool.beq_eq_decide_eq]
  · have hn : w ≠ p.val := by have := p.isLt; omega
    have hnl : N ≤ w := by omega
    simp [hl, hnl, hn, Bool.beq_eq_decide_eq]

lemma markedMissing {N : ℕ} (C : Circuit) (p l : Fin N) {w : ℕ}
    (hm : N + N + C.size ≤ w) : markedValue C p l w = (false,false) :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, markedStart_length, Circuit.size] using hm)

lemma markedGate {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (p l : Fin N) (k : Fin C.size) :
    markedValue C p l (outWire (N+N) k) = markedOp (row C k).op
        [markedValue C p l (operand C k 0), markedValue C p l (operand C k 1)] :=
  evalFrom_gate _ _ h _ (markedStart_length p l) k

lemma marked_count {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (p l : Fin N) (w : ℕ) (t : List ℕ) (ht : t ∈ words (N+N) C w)
    (hs : ∀ i ∈ t, i ∈ [p.val, N+l.val]) :
    (t.count (N+l.val) = 0 → (markedValue C p l w).1 = true) ∧
    (t.count (N+l.val) = 1 → (markedValue C p l w).2 = true) := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases (N+N) C.size w with hw | ⟨k,rfl⟩ | hm
    · rw [words_input C hw] at ht
      have ht' : t = [w] := ht
      subst t
      have hs' : w = p.val ∨ w = N+l.val := by simpa using hs w (by simp)
      rw [markedInput C p l hw]
      rcases hs' with rfl | rfl
      · have hn : p.val ≠ N+l.val := by have := p.isLt; omega
        simp [p.isLt, hn]
      · have hn : ¬N+l.val < N := by omega
        simp [hn]
    · rw [words_gate h k] at ht
      rw [markedGate h p l k]
      rcases op_kind h k with ho | ho
      · rw [ho] at ht ⊢
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        have hs₀ : ∀ i ∈ u, i ∈ [p.val, N+l.val] :=
          fun i hi => hs i (List.mem_append_left _ hi)
        have hs₁ : ∀ i ∈ v, i ∈ [p.val, N+l.val] :=
          fun i hi => hs i (List.mem_append_right _ hi)
        obtain ⟨hu₀,hu₁⟩ := ih _ (earlier h k 0) _ hu hs₀
        obtain ⟨hv₀,hv₁⟩ := ih _ (earlier h k 1) _ hv hs₁
        constructor
        · intro hz
          have hu0 : u.count (N+l.val) = 0 := by rw [List.count_append] at hz; omega
          have hv0 : v.count (N+l.val) = 0 := by rw [List.count_append] at hz; omega
          simp [markedOp, hu₀ hu0, hv₀ hv0]
        · intro hz
          have he : (u.count (N+l.val) = 0 ∧ v.count (N+l.val) = 1) ∨
              (u.count (N+l.val) = 1 ∧ v.count (N+l.val) = 0) := by
            rw [List.count_append] at hz
            omega
          rcases he with ⟨hu0,hv1⟩ | ⟨hu1,hv0⟩
          · simp [markedOp, hu₀ hu0, hv₁ hv1]
          · simp [markedOp, hu₁ hu1, hv₀ hv0]
      · rw [ho] at ht ⊢
        rcases ht with ht | ht
        · obtain ⟨h0,h1⟩ := ih _ (earlier h k 0) _ ht hs
          constructor
          · intro hz; simp [markedOp, h0 hz]
          · intro hz; simp [markedOp, h1 hz]
        · obtain ⟨h0,h1⟩ := ih _ (earlier h k 1) _ ht hs
          constructor
          · intro hz; simp [markedOp, h0 hz]
          · intro hz; simp [markedOp, h1 hz]
    · simp [words_missing (N+N) C hm] at ht

lemma word_lineSingle {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (p l : Fin N) (t : List ℕ) (ht : t ∈ words (N+N) C C.output)
    (hs : ∀ i ∈ t, i ∈ [p.val, N+l.val]) (hc : t.count (N+l.val) = 1) :
    lineSingle C (N+N) (fun w => decide (N≤w)) p.val (N+l.val) = true :=
  (marked_count h p l C.output t ht hs).2 hc

end SingleLine

section CoreWitness

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK

lemma graph_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) : graphFun G ∅ (fun i => decide (i=a)) = false := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨u,v,huv,hu,hv⟩
  have hu' : u=a := of_decide_eq_true hu
  have hv' : v=a := of_decide_eq_true hv
  subst u
  subst v
  exact G.loopless.irrefl a huv

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (h : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u,v,h,by simp [pairInput],by simp [pairInput]⟩

lemma value_eq_gateVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    circuitValue C x (n+j) = gateVal n C j x := rfl

lemma value_eq_eval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    circuitValue C x w = Circuit.eval ⟨C.gates,w⟩ (List.ofFn x) := rfl

lemma word_both_endpoints {N : ℕ} (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj]
    {C : Circuit} (h : IsAO2 (N+N) C) (p l : Fin N) (w : ℕ)
    (hb : ∀ x : Fin (N+N) → Bool, circuitValue C x w = true → graphFun G ∅ x = true)
    (t : List ℕ) (ht : t ∈ words (N+N) C w)
    (hs : ∀ i ∈ t, i ∈ [p.val,N+l.val]) : N+l.val ∈ t := by
  by_contra hn
  have hz : circuitValue C (fun i : Fin (N+N) => decide (i=Fin.castAdd N p)) w = true := by
    apply (value_eq_terms h _ w).mpr
    refine ⟨t,ht,?_⟩
    intro i hi
    have he : i=p.val := by
      rcases (by simpa using hs i hi : i=p.val ∨ i=N+l.val) with hp | hl
      · exact hp
      · exact False.elim (hn (hl ▸ hi))
    exact ⟨Fin.castAdd N p,he.symm,by simp⟩
  have hf := hb _ hz
  rw [graph_singleton] at hf
  cases hf

end CoreWitness


section FirstAnd

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK

lemma below_first_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
    (hb : ∀ y : Fin n → Bool, circuitValue C y w = true → graphFun G ∅ y = true)
    (hv : circuitValue C x w = true) (hs : words n C w ⊆ words n C C.output) :
    ∃ k : Fin C.size, (row C k).op = GateOp.and ∧
      (∀ y : Fin n → Bool, circuitValue C y (outWire n k) = true → graphFun G ∅ y = true) ∧
      circuitValue C x (outWire n k) = true ∧
      words n C (outWire n k) ⊆ words n C C.output := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hw | ⟨k,rfl⟩ | hm
    · have ht : circuitValue C (fun i : Fin n => decide (i=⟨w,hw⟩)) w = true := by
        rw [value_input C _ hw]
        simp
      have hf := hb _ ht
      rw [graph_singleton] at hf
      cases hf
    · rcases op_kind h k with ho | ho
      · exact ⟨k,ho,hb,hv,hs⟩
      · have hb' (b : Fin 2) : ∀ y : Fin n → Bool,
            circuitValue C y (operand C k b) = true → graphFun G ∅ y = true := by
          intro y hy
          apply hb y
          rw [value_gate h y k, ho]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
          fin_cases b
          · exact Or.inl hy
          · exact Or.inr hy
        have hs' (b : Fin 2) : words n C (operand C k b) ⊆ words n C C.output := by
          intro t ht
          apply hs
          rw [words_gate h k, ho]
          fin_cases b
          · exact Or.inl ht
          · exact Or.inr ht
        have hv' : circuitValue C x (operand C k 0) = true ∨
            circuitValue C x (operand C k 1) = true := by
          simpa [value_gate h x k, ho, GateOp.eval] using hv
        rcases hv' with hv' | hv'
        · exact ih _ (earlier h k 0) (hb' 0) hv' (hs' 0)
        · exact ih _ (earlier h k 1) (hb' 1) hv' (hs' 1)
    · rw [value_missing C x hm] at hv
      cases hv

lemma and_witness_core {N : ℕ} (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj]
    {C : Circuit} (h : IsAO2 (N+N) C) (p l : Fin N)
    (hadj : G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (hn : ∀ k2 < C.gates.length, (gateAt C k2).op = GateOp.and →
      ∀ t ∈ (gateAt C k2).inputs, ¬ (∀ x : Fin (N+N) → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (hl : lineSingle C (N+N) (fun w => decide (N≤w)) p.val (N+l.val) = false)
    (k : Fin C.size) (ho : (row C k).op = GateOp.and)
    (hb : ∀ x : Fin (N+N) → Bool,
      circuitValue C x (outWire (N+N) k) = true → graphFun G ∅ x = true)
    (hv : circuitValue C (pairInput (Fin.castAdd N p) (Fin.natAdd N l))
      (outWire (N+N) k) = true)
    (hs : words (N+N) C (outWire (N+N) k) ⊆ words (N+N) C C.output) :
    IsCore G C k.val := by
  have hrow : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hopnd (b : Fin 2) : opnd C k.val b = operand C k b := by
    simp only [opnd, operand, hrow]
  have hnot : ¬ (IsImpOperand G C (opnd C k.val 0) ∧
      IsImpOperand G C (opnd C k.val 1)) := by
    intro hi
    have hmem : opnd C k.val 0 ∈ (gateAt C k.val).inputs := by
      rw [hrow, inputs_two h k, hopnd]
      simp
    apply hn k.val k.isLt (by simpa only [hrow] using ho) _ hmem
    intro x hx
    apply hi.1.2.1 x
    have he : N+N+(opnd C k.val 0-(N+N)) = opnd C k.val 0 :=
      Nat.add_sub_of_le hi.1.1
    simpa only [gateVal, Circuit.eval, Circuit.wires, he] using hx
  refine ⟨k.isLt,⟨hb,⟨_,hv⟩⟩,hnot,Fin.castAdd N p,Fin.natAdd N l,hadj,hv,?_⟩
  unfold ReadTwiceAt
  cases he : readsAtMost (atGate (N+N) C k.val) (N+N)
      [(Fin.castAdd N p).val,(Fin.natAdd N l).val] 1 with
  | false => rfl
  | true =>
    have hat : IsAO2 (N+N) (atGate (N+N) C k.val) := h
    obtain ⟨t,ht,hts,hcount⟩ := read_to_terms hat [p.val,N+l.val] he
    have ht' : t ∈ words (N+N) C (outWire (N+N) k) := ht
    have hmem := word_both_endpoints G h p l (outWire (N+N) k) hb t ht' hts
    have hpos : 0 < t.count (N+l.val) := List.count_pos_iff.mpr hmem
    have hle : t.count (N+l.val) ≤ 1 := hcount _ (by simp)
    have hc : t.count (N+l.val) = 1 := by omega
    have htrue := word_lineSingle h p l t (hs ht') hts hc
    rw [hl] at htrue
    cases htrue

theorem core_for_doubleReread
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (C : Circuit)
    (hI : ∀ u v : Fin (N+N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
      ((u=Fin.castAdd N p ∧ v=Fin.natAdd N l) ∨
       (u=Fin.natAdd N l ∧ v=Fin.castAdd N p)))
    (h : IsAO2 (N+N) C)
    (hF : circuitFun (N+N) C = graphFun G ∅)
    (hn : ∀ k2 < C.gates.length, (gateAt C k2).op = GateOp.and →
      ∀ t ∈ (gateAt C k2).inputs, ¬ (∀ x : Fin (N+N) → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (p l : Fin N)
    (hd : (p.val,N+l.val) ∈ doubleReread C (N+N) (fun w => decide (N≤w))
      ((List.finRange N).flatMap fun a =>
        ((List.finRange N).filter fun b => decide (I a b)).map fun b => (a.val,N+b.val))) :
    ∃ j, IsCore G C j ∧ s(Fin.castAdd N p,Fin.natAdd N l) ∈ gammaE G C j := by
  obtain ⟨he,hd⟩ := List.mem_filter.mp hd
  obtain ⟨a,ha,hmem⟩ := List.mem_flatMap.mp he
  obtain ⟨b,hb,heq⟩ := List.mem_map.mp hmem
  have hap : a=p := Fin.ext (congrArg Prod.fst heq)
  have hbl : b=l := Fin.ext (by have hh := congrArg Prod.snd heq; dsimp at hh; omega)
  subst a
  subst b
  have hip : I p l := of_decide_eq_true (List.mem_filter.mp hb).2
  have hadj : G.Adj (Fin.castAdd N p) (Fin.natAdd N l) :=
    (hI _ _).mpr ⟨p,l,hip,Or.inl ⟨rfl,rfl⟩⟩
  have hl : lineSingle C (N+N) (fun w => decide (N≤w)) p.val (N+l.val) = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
    exact hd.1
  have hbelow : ∀ x : Fin (N+N) → Bool,
      circuitValue C x C.output = true → graphFun G ∅ x = true := by
    intro x hx
    have he := congrFun hF x
    exact he ▸ hx
  have hval : circuitValue C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) C.output = true := by
    change circuitFun (N+N) C _ = true
    rw [hF]
    exact graph_pair G _ _ hadj
  obtain ⟨k,ho,hbelow',hv,hs⟩ := below_first_and G h _ C.output hbelow hval (fun _ hh => hh)
  refine ⟨k.val,and_witness_core G h p l hadj hn hl k ho hbelow' hv hs,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_,Fin.castAdd N p,Fin.natAdd N l,rfl,hv⟩
  simpa using hadj

end FirstAnd

end PEqualNP.Outside.L_meta_3652.ReadWitness

theorem PEqualNP.Outside.L_meta_3652 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := by
  intro N I _ G _ C hI _ hAO hF hfixed hlive hno p l hd
  obtain ⟨j, hcore, hgamma⟩ :=
    PEqualNP.Outside.L_meta_3652.ReadWitness.core_for_doubleReread
      N I G C hI hAO hF hno p l hd
  exact PEqualNP.Outside.L_meta_3652.Structure.maximal_core_accepts
    hAO hfixed hlive hno hcore hgamma
