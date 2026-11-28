import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47887.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

theorem canalize_left {R u d} (hd : allowed u d) (w : Bool → Wire R) :
    ∃ t, Constant (comb d (fun _ => t) (w t)) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by funext r; simp [comb, combine]⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by funext r; simp [comb, combine, inv]⟩

theorem canalize_right {R u d} (hd : allowed u d) (w : Bool → Wire R) :
    ∃ t, Constant (comb d (w t) (fun _ => t)) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by funext r; simp [comb, combine, inv]⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩

theorem contract_two {R S : Type} {u} {goal pivot : Wire R} {s ws}
    (run : Run u goal s ws) (rows : Bool → S → R)
    (value : ∀ b, restrictRows (rows b) pivot = (fun _ => b))
    (nonconstant : ∀ b, ¬Constant (restrictRows (rows b) goal))
    (occurs : pivot ∈ ws)
    (roots : Bool → List (Wire S)) {p : Nat} (banks : Bool → List (Wire S))
    (reached : ∀ b, Reach u (roots b) p (banks b))
    (supplied : ∀ b, supply u (banks b) (ws.map (restrictRows (rows b)))) :
    ∃ b q next, Reach u (roots b) q next ∧
      Available u next (restrictRows (rows b) goal) ∧ q+2 ≤ p+s := by
  induction run using Run.ind generalizing p banks with
  | stop =>
    have e : pivot = goal := List.mem_singleton.mp occurs
    exact False.elim (nonconstant false ⟨false, e ▸ value false⟩)
  | perm permutation _ ih =>
    apply ih (permutation.mem_iff.mpr occurs) banks reached
    intro b a ha
    exact supplied b a ((permutation.map _).mem_iff.mp ha)
  | @two steps a b rest op hd ka kb tail ih =>
    let next := comb op a b :: kept ka a (kept kb b rest)
    have pairA (t : Bool) : Available u (banks t) (restrictRows (rows t) a) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have pairB (t : Bool) : Available u (banks t) (restrictRows (rows t) b) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have held (t : Bool) {pool} (stable : ∀ w, Available u (banks t) w → Available u pool w)
        (head : Available u pool (restrictRows (rows t) (comb op a b))) :
        supply u pool (next.map (restrictRows (rows t))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | keep
      · exact head
      · apply stable
        apply supplied
        apply List.mem_map_of_mem
        rcases mem_kept keep with rfl | keep
        · simp
        · rcases mem_kept keep with rfl | keep
          · simp
          · simp [keep]
    by_cases used : pivot = a ∨ pivot = b
    · have choose : ∃ t, Constant (restrictRows (rows t) (comb op a b)) := by
        rcases used with eq | eq
        · subst a
          obtain ⟨t, hc⟩ := canalize_left hd (fun t => restrictRows (rows t) b)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
        · subst b
          obtain ⟨t, hc⟩ := canalize_right hd (fun t => restrictRows (rows t) a)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
      obtain ⟨t, hc⟩ := choose
      have sp := held t (fun _ h => h) (Or.inr (Or.inl hc))
      obtain ⟨q, out, reach, found, smaller⟩ :=
        contraction (nonconstant t) (restrict_run (rows t) tail) (roots t) (reached t) sp
      have one : 1 ≤ mass (next.map (restrictRows (rows t))) := by
        classical
        simp [next, mass_cons, cost, hc]
      dsimp only [next] at one
      exact ⟨t, q, out, reach, found, by omega⟩
    · have inRest : pivot ∈ rest := by simpa [List.mem_cons, not_or.mp used] using occurs
      have inNext : pivot ∈ next := by cases ka <;> cases kb <;> simp [next, kept, inRest]
      have all (t : Bool) : ∃ pool, Reach u (roots t) (p+1) pool ∧
          supply u pool (next.map (restrictRows (rows t))) := by
        obtain ⟨binOp, x, y, eq, hx, hy, _, _⟩ := comb_prime hd (pairA t) (pairB t)
        have new := Reach.two binOp (reached t) hx hy
        refine ⟨_, new, held t (fun _ h => available_cons _ h) ?_⟩
        rw [restrict_comb, eq]
        exact Or.inl (by simp)
      choose pools reach sp using all
      obtain ⟨t, q, out, rch, found, smaller⟩ := ih inNext pools reach sp
      exact ⟨t, q, out, rch, found, by omega⟩

abbrev Row := Fin 64
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
theorem input_list : List.ofFn (fun j : Fin 6 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 64-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(64-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 64 (64-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 64-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 6).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def fixRows (z o : Nat) : List Move :=
  (List.range 6).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 64 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 64 d)

theorem lower_two_slices {u roots T pivot L}
    (properT : proper T) (plainT : plainWord T = true) (plainRoots : roots.all plainWord = true)
    (essential : Essential T roots pivot) (rows : Bool → Row → Row)
    (sub : Bool → List Sig) (goals : Bool → Sig)
    (mapTarget : ∀ b, rename (rows b) T = goals b)
    (mapRoots : ∀ b a, a ∈ roots → Available u ((sub b).map observe) (observe (rename (rows b) a)))
    (value : ∀ b, restrictRows (rows b) (observe pivot) = (fun _ => b))
    (properGoals : ∀ b, proper (goals b))
    (bounds : ∀ b, Lower u (sub b) (goals b) L) :
    Lower u roots T (L+2) := by
  intro p bank reachable hit
  obtain ⟨k, states, le, live, root⟩ := reach_live properT plainT plainRoots reachable hit
  obtain ⟨i, j, different, isolated⟩ := essential
  have pivotMem := raw_required live roots pivot root i j different isolated
  let front := states.toList.map observe
  have run : Run u (observe T) k front :=
    list_run live states.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have occurs : observe pivot ∈ front :=
    List.mem_map_of_mem (Finset.mem_toList.mpr pivotMem)
  have target (b : Bool) : restrictRows (rows b) (observe T) = observe (goals b) :=
    (observe_rename (rows b) T).symm.trans (congrArg observe (mapTarget b))
  have nonconstant (b : Bool) : ¬Constant (restrictRows (rows b) (observe T)) := by
    rw [target]
    exact observe_proper (properGoals b)
  let banks := fun b => (sub b).map observe
  have covered (b : Bool) : supply u (banks b) (front.map (restrictRows (rows b))) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [←observe_rename]
    exact mapRoots b w (root _ (Finset.mem_toList.mp hw))
  obtain ⟨b, q, out, reached, got, weighted⟩ :=
    contract_two run rows value nonconstant occurs banks banks (fun _ => Reach.start) covered
  rw [target] at got
  have enough := bounds b q out reached got
  omega

theorem lower_cubes_two {u raw base0 base1 T G0 G1 j L r s z0 o0 z1 o1}
    (essential : checkEssential T raw [(inputs.getD j zero, r, s)] = true)
    (lowMap : checkMap (fixRows z0 o0) raw T base0 G0 = true)
    (highMap : checkMap (fixRows z1 o1) raw T base1 G1 = true)
    (lowBit : movedWord (fixRows z0 o0) (inputs.getD j zero) = zero)
    (highBit : movedWord (fixRows z1 o1) (inputs.getD j zero) = one)
    (properT : proper T) (proper0 : proper G0) (proper1 : proper G1)
    (low : Lower u base0 G0 L) (high : Lower u base1 G1 L) : Lower u raw T (L+2) := by
  let moves : Bool → List Move := fun b => if b then fixRows z1 o1 else fixRows z0 o0
  let sub : Bool → List Sig := fun b => if b then base1 else base0
  let goal : Bool → Sig := fun b => if b then G1 else G0
  have maps (b : Bool) : checkMap (moves b) raw T (sub b) (goal b) = true := by
    cases b
    · exact lowMap
    · exact highMap
  apply lower_two_slices properT (essential_plain essential).1 (essential_plain essential).2
    (essential_ok essential (inputs.getD j zero) (by simp)) (fun b => movedRow (moves b)) sub goal
  · exact fun b => (map_correct (u:=u) (maps b)).1
  · exact fun b => (map_correct (u:=u) (maps b)).2
  · intro b
    rw [←observe_rename, ←moved_eq_rename]
    cases b <;> change observe (movedWord _ _) = _
    · rw [show movedWord (moves false) (inputs.getD j zero) = zero from lowBit]
      exact funext bit_zero
    · rw [show movedWord (moves true) (inputs.getD j zero) = one from highBit]
      exact funext bit_one
  · intro b
    cases b
    · exact proper0
    · exact proper1
  · intro b
    cases b
    · exact low
    · exact high

theorem lower_fix_two {u raw base0 base1 T G0 G1 j L r s}
    (essential : checkEssential T raw [(inputs.getD j zero, r, s)] = true)
    (lowMap : checkMap (fixRows (1 <<< j) 0) raw T base0 G0 = true)
    (highMap : checkMap (fixRows 0 (1 <<< j)) raw T base1 G1 = true)
    (lowBit : movedWord (fixRows (1 <<< j) 0) (inputs.getD j zero) = zero)
    (highBit : movedWord (fixRows 0 (1 <<< j)) (inputs.getD j zero) = one)
    (properT : proper T) (proper0 : proper G0) (proper1 : proper G1)
    (low : Lower u base0 G0 L) (high : Lower u base1 G1 L) : Lower u raw T (L+2) :=
  lower_cubes_two essential lowMap highMap lowBit highBit properT proper0 proper1 low high

theorem lower_weaken {u roots T m n} (lower : Lower u roots T m) (le : n ≤ m) :
    Lower u roots T n :=
  fun p bank reached hit => le.trans (lower p bank reached hit)

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 128
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 128 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 128 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 128 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 128 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def asRow (cols : Nat → Bits) (i : Fin 128) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 6 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem input_coords : ∀ (j : Fin 6) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 128) (j : Fin 6) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 6 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<6 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun n w => n+keyWord w) 0

theorem contract_two_cost {R S : Type} {u} {goal pivot : Wire R} {s ws}
    (run : Run u goal s ws) (rows : Bool → S → R)
    (value : ∀ b, restrictRows (rows b) pivot = (fun _ => b))
    (nonconstant : ∀ b, ¬Constant (restrictRows (rows b) goal))
    (occurs : pivot ∈ ws)
    (roots : Bool → List (Wire S)) {charges : Bool → Nat} (banks : Bool → List (Wire S))
    (reached : ∀ b, Reach u (roots b) (charges b) (banks b))
    (supplied : ∀ b, supply u (banks b) (ws.map (restrictRows (rows b)))) :
    ∃ b q next, Reach u (roots b) q next ∧
      Available u next (restrictRows (rows b) goal) ∧ q+2 ≤ charges b+s := by
  induction run using Run.ind generalizing charges banks with
  | stop =>
    have e : pivot = goal := List.mem_singleton.mp occurs
    exact False.elim (nonconstant false ⟨false, e ▸ value false⟩)
  | perm permutation _ ih =>
    apply ih (permutation.mem_iff.mpr occurs) banks reached
    intro b a ha
    exact supplied b a ((permutation.map _).mem_iff.mp ha)
  | @two steps a b rest op hd ka kb tail ih =>
    let next := comb op a b :: kept ka a (kept kb b rest)
    have pairA (t : Bool) : Available u (banks t) (restrictRows (rows t) a) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have pairB (t : Bool) : Available u (banks t) (restrictRows (rows t) b) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have held (t : Bool) {pool} (stable : ∀ w, Available u (banks t) w → Available u pool w)
        (head : Available u pool (restrictRows (rows t) (comb op a b))) :
        supply u pool (next.map (restrictRows (rows t))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | keep
      · exact head
      · apply stable
        apply supplied
        apply List.mem_map_of_mem
        rcases mem_kept keep with rfl | keep
        · simp
        · rcases mem_kept keep with rfl | keep
          · simp
          · simp [keep]
    by_cases used : pivot = a ∨ pivot = b
    · have choose : ∃ t, Constant (restrictRows (rows t) (comb op a b)) := by
        rcases used with eq | eq
        · subst a
          obtain ⟨t, hc⟩ := canalize_left hd (fun t => restrictRows (rows t) b)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
        · subst b
          obtain ⟨t, hc⟩ := canalize_right hd (fun t => restrictRows (rows t) a)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
      obtain ⟨t, hc⟩ := choose
      have sp := held t (fun _ h => h) (Or.inr (Or.inl hc))
      obtain ⟨q, out, reach, found, smaller⟩ :=
        contraction (nonconstant t) (restrict_run (rows t) tail) (roots t) (reached t) sp
      have one : 1 ≤ mass (next.map (restrictRows (rows t))) := by
        classical
        simp [next, mass_cons, cost, hc]
      dsimp only [next] at one
      exact ⟨t, q, out, reach, found, by omega⟩
    · have inRest : pivot ∈ rest := by simpa [List.mem_cons, not_or.mp used] using occurs
      have inNext : pivot ∈ next := by cases ka <;> cases kb <;> simp [next, kept, inRest]
      have all (t : Bool) : ∃ pool, Reach u (roots t) (charges t+1) pool ∧
          supply u pool (next.map (restrictRows (rows t))) := by
        obtain ⟨binOp, x, y, eq, hx, hy, _, _⟩ := comb_prime hd (pairA t) (pairB t)
        have new := Reach.two binOp (reached t) hx hy
        refine ⟨_, new, held t (fun _ h => available_cons _ h) ?_⟩
        rw [restrict_comb, eq]
        exact Or.inl (by simp)
      choose pools reach sp using all
      obtain ⟨t, q, out, rch, found, smaller⟩ := ih inNext (charges := fun t => charges t + 1) pools reach sp
      exact ⟨t, q, out, rch, found, by omega⟩

def dualPoolCut (c0 c1 : BoundPool) (cap : Nat) (ws : List Sig) : Bool :=
  decide (cap + c0.paid < c0.bound + 2) &&
  (decide (cap + c1.paid < c1.bound + 2) &&
  (ws.all (availableB true c0.domain c0.wires) &&
  (ws.all (availableB true c1.domain c1.wires) &&
  ws.any (fun pivot => masked c0.domain pivot == zero && masked c1.domain pivot == c1.domain))))

theorem dualPoolCut_sound {raw T c0 c1 cap ws}
    (valid0 : ValidPool true raw T c0) (valid1 : ValidPool true raw T c1)
    (nd : ws.Nodup) (test : dualPoolCut c0 c1 cap ws = true) :
    Impossible true T cap ws.toFinset := by
  intro steps hcap run
  simp only [dualPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, beq_iff_eq] at test
  obtain ⟨small0, small1, all0, all1, pivot, hpivot, zeroed, oned⟩ := test
  obtain ⟨f0, roots0, bank0, dom0, nc0, low0, paid0, avail0, _⟩ := valid0
  obtain ⟨f1, roots1, bank1, dom1, nc1, low1, paid1, avail1, _⟩ := valid1
  let rows : Bool → Row → Row := fun b => if b then f1 else f0
  let roots : Bool → List (Wire Row) := fun b => if b then roots1.map observe else roots0.map observe
  let banks : Bool → List (Wire Row) := fun b => if b then bank1 else bank0
  let charges : Bool → Nat := fun b => if b then c1.paid else c0.paid
  have nonconstant (b : Bool) : ¬Constant (restrictRows (rows b) (observe T)) := by
    cases b
    · exact nc0
    · exact nc1
  have value (b : Bool) : restrictRows (rows b) (observe pivot) = (fun _ => b) := by
    cases b
    · exact masked_zero dom0 zeroed
    · exact masked_one dom1 oned
  have reached (b : Bool) : Reach true (roots b) (charges b) (banks b) := by
    cases b
    · exact paid0
    · exact paid1
  have supplied (b : Bool) : supply true (banks b) ((ws.map observe).map (restrictRows (rows b))) := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    cases b
    · exact availableB_sound dom0 avail0 (all0 v hv)
    · exact availableB_sound dom1 avail1 (all1 v hv)
  have occurs : observe pivot ∈ ws.map observe := List.mem_map_of_mem hpivot
  obtain ⟨b, q, next, reach, hit, weighted⟩ :=
    contract_two_cost (list_run run ws nd rfl) rows value nonconstant occurs roots (charges := charges) banks reached supplied
  cases b
  · have enough := low0 q next reach hit
    change q + 2 ≤ c0.paid + steps at weighted
    omega
  · have enough := low1 q next reach hit
    change q + 2 ≤ c1.paid + steps at weighted
    omega

abbrev CutData := BoundPool × Option BoundPool
def ValidCut (u : Bool) (raw : List Sig) (T : Sig) (c : CutData) :=
  ValidPool u raw T c.1 ∧ ∀ b, c.2 = some b → u = true ∧ ValidPool true raw T b

def cutTest (u : Bool) (c : CutData) (k : Nat) (rest : List Sig) (op : Choice) :=
  match c.2 with
  | none => scalarPoolCut u c.1 k rest op
  | some b => dualPoolCut c.1 b k (choiceVal op :: rest)

theorem cutTest_sound {u raw T c k rest op} (v : ValidCut u raw T c)
    (nd : (choiceVal op :: rest).Nodup) (check : cutTest u c k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  cases h : c.2 with
  | none =>
    simp only [cutTest,h] at check
    exact scalarPoolCut_sound v.1 nd check
  | some b =>
    obtain ⟨rfl,hb⟩ := v.2 b h
    simp only [cutTest,h] at check
    exact dualPoolCut_sound v.1 hb nd check

def closeChild (u : Bool) (pools : Nat → List CutData) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || (pools (keySet ws)).any (fun p => cutTest u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact cutTest_sound (pValid _ _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × (Nat → List CutData) × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 128 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 128) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 128 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<6
  · let i : Fin 6 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 64 ≤ 2^j := by
      change 2^6 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

theorem reflectState {u T k} (ws : List Sig) (p : List Move)
    (ok : autoOK T p = true) (low : Impossible u T k ws.toFinset) :
    Impossible u T k (ws.map (movedWord p.reverse)).toFinset := rotate_excluded low p ok

abbrev Observed (p q : Fin 128 → Row) := {v : Decor // faithful p q v}

def inputObserved (m : Nat) (p q : Nat → Bits) (i : Nat) :
    Observed (asRow p) (asRow q) :=
  ⟨(rawDecor m p q).getD i defaultDecor, faithful_get (raw_faithful m p q) i⟩

def combineObserved {p q} (d : Nat) (a b : Observed p q) : Observed p q :=
  ⟨dbin d a.val b.val, faithful_bin d a.property b.property⟩

abbrev Closed (T : Sig) (k : Nat) := { ws : List Sig // Impossible true T k ws.toFinset }
def rotateClosed {T k} (c : Closed T k) (p : List Move)
    (ok : autoOK T p = true) : Closed T k :=
  ⟨c.val.map (movedWord p.reverse), rotate_excluded c.property p ok⟩

abbrev Pool (raw : List Sig) (T : Sig) := { c : BoundPool // ValidPool true raw T c }

def checkedPool {raw T dom n} (slice : Slice true raw T dom n)
    (cs : List Choice) (c : BoundPool) (ok : materialize true raw cs dom n = some c) : Pool raw T :=
  ⟨c, materialize_sound slice ok⟩

def prefixPool {raw T d n} (slice : Slice true raw T d n) (cs : List Choice)
    (ok : makePool true d raw cs = some (cs.reverse.map choiceVal ++ raw)) : Pool raw T :=
  checkedPool slice cs (d,n,cs.length,cs.reverse.map choiceVal ++ raw)
    (by simp only [materialize,ok,Option.map_some,Option.some.injEq])

abbrev ChosenPool (raw : List Sig) (T : Sig) := {c : CutData // ValidCut true raw T c}
def usePool {raw T} (p : Pool raw T) : ChosenPool raw T :=
  ⟨(p.val,none),p.property,by simp⟩
def joinPools {raw T} (p q : Pool raw T) : ChosenPool raw T :=
  ⟨(p.val,some q.val),p.property,by
    intro b hb
    change some q.val = some b at hb
    cases Option.some.inj hb
    exact ⟨rfl,q.property⟩⟩
def stateCheck {p q T raw} (k : Nat) (ws : List (Observed p q))
    (route : Nat → List (ChosenPool raw T) × List (Closed T (k-1))) : Bool :=
  let items := ws.map Subtype.val
  let vs := items.map Prod.fst
  decide vs.Nodup && !vs.contains T &&
    testAll (k, items.length, items, preCov true items, (fun h => (route h).1.map Subtype.val),
      fun h => (route h).2.map Subtype.val) items

def closeState {T raw p q} (pairs : properPairs T p q) (k : Nat) (ws : List (Observed p q))
    (route : Nat → List (ChosenPool raw T) × List (Closed T (k-1)))
    (ok : stateCheck k ws route = true) : Closed T k := by
  let items := ws.map Subtype.val
  refine ⟨items.map Prod.fst, ?_⟩
  simp only [stateCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at ok
  apply node_sound (raw := raw) pairs _ ok.1.1 ok.1.2 _ _ ok.2
  · intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact a.property
  · intro _ c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact a.property
  · intro _ ys hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact a.property

def chooseRoute {α β : Type} (p : Array α) (below : Array β) (i : Nat) : List α × List β :=
  if i < p.size then ((p[i]?).toList, []) else ([],(below[i-p.size]?).toList)

theorem fromClosed {raw T k} (c : Closed T k)
    (names : c.val.toFinset = raw.toFinset) (xs : List (Sig × Row × Row))
    (pr : proper T) (check : checkEssential T raw xs = true) (all : xs.map Prod.fst = raw) :
    Lower true raw T (k+1) := by
  apply lower_impossible pr (essential_plain check).1 (essential_plain check).2
  · intro a ha
    exact essential_ok check a (List.mem_toFinset.mpr (all ▸ ha))
  · rw [← names]
    exact c.property

end PEqualNP.Outside.L_meta_47887.Model
namespace PEqualNP.Outside.L_meta_47887
open PEqualNP.Outside.L_meta_47887.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Prior51812B0
def R : List Sig := vars 23
def T : Sig := 0x8888808088888080
theorem low : Lower true R T 3 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xffff0000ffff0000, 3, 19)] (by decide +kernel)
end Prior51812B0

namespace Prior51812B4
def R : List Sig := vars 7
def T : Sig := 0xe8e8e8e8e8e8e8e8
def P : Nat → Bits
  | 0 => ((0xbecfbecfbecfbecf : BitVec 64) ++ (0xbecfbecfbecfbecf : BitVec 64))
  | 1 => ((0xdf73df73df73df73 : BitVec 64) ++ (0xdf73df73df73df73 : BitVec 64))
  | 2 => ((0xefbcefbcefbcefbc : BitVec 64) ++ (0xefbcefbcefbcefbc : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x4205420542054205 : BitVec 64) ++ (0x4205420542054205 : BitVec 64))
  | 1 => ((0x2412241224122412 : BitVec 64) ++ (0x2412241224122412 : BitVec 64))
  | 2 => ((0x1828182818281828 : BitVec 64) ++ (0x1828182818281828 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 7 P N 0
def w1 := inputObserved 7 P N 1
def w2 := inputObserved 7 P N 2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2]
  (fun _ => ([], [])) (by decide +kernel)
theorem low : Lower true R T 4 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end Prior51812B4

namespace Prior51812B5
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) Prior51812B4.low
end Prior51812B5

namespace Prior51812B8
def R : List Sig := vars 15
def T : Sig := 0xe8a8e8a8e8a8e8a8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 6, 14)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) Prior51812B4.low
  have he : (([(0xff00ff00ff00ff00, 6, 14)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end Prior51812B8

namespace Prior51812B15
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) Prior51812B4.low
end Prior51812B15

namespace Prior51812B19
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) Prior51812B4.low
end Prior51812B19

namespace Prior51812B25
def R : List Sig := vars 11
def T : Sig := 0x8800880088008800
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 9, 11), (0xff00ff00ff00ff00, 3, 11)] (by decide +kernel)
end Prior51812B25

namespace Prior51812B26
def R : List Sig := vars 15
def T : Sig := 0xe880e880e880e880
def P : Nat → Bits
  | 0 => ((0xfc7fefee3fff8ff8 : BitVec 64) ++ (0xffdfdc7fff1ff1ff : BitVec 64))
  | 1 => ((0xff8ff7f7c7fff1ff : BitVec 64) ++ (0x1fefef8fffe3fe3f : BitVec 64))
  | 2 => ((0x1ff1fbfbf8fffe3f : BitVec 64) ++ (0xe3f7f7f1fffc7fc7 : BitVec 64))
  | 3 => ((0xe3fe3dfdff1fffc7 : BitVec 64) ++ (0xfc7bfbfe3fff8ff8 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x2436d021c9258248 : BitVec 64) ++ (0x6da043924b0490db : BitVec 64))
  | 1 => ((0x498b48407a4a9093 : BitVec 64) ++ (0x169080f49521262d : BitVec 64))
  | 2 => ((0x12d1848097932425 : BitVec 64) ++ (0xa309012f26484b46 : BitVec 64))
  | 3 => ((0x836c030124fc4906 : BitVec 64) ++ (0xd8060249f8920db0 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xcccccccccccccccc 4 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B15.low
def p0 : Pool R T := checkedPool s0 []
  (0xcccccccccccccccc, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s1 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B5.low
def p1 : Pool R T := checkedPool s1 []
  (0xaaaaaaaaaaaaaaaa, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 0 w0 w2
def w6 := combineObserved 0 w1 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w4, w5, w6, w3]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B4.low
def p2 : Pool R T := checkedPool s2 []
  (0xff00ff00ff00ff00, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 2 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B25.low
def p3 : Pool R T := checkedPool s3 []
  (0xf0f0f0f0f0f0f0f, 2, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 4 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B19.low
def p4 : Pool R T := checkedPool s4 [(0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (3, 0x8080808080808080, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f0, 4, 2, [0x7f007f007f007f00, 0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def w7 := combineObserved 0 w4 w2
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w7, w0, w1, w2, w3]
  (fun _ => ([(usePool p2), (joinPools p3 p4)], [])) (by decide +kernel)
def w8 := combineObserved 0 w2 w3
def w9 := combineObserved 3 w8 w0
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w9, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := checkedPool s4 []
  (0xf0f0f0f0f0f0f0f0, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w4, w5, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p5)] #[v0] ((((0x84 : Nat) >>> ((h % 9) * 2)) &&& 3))) (by decide +kernel)
def a0 : List Move := [swapRows 33, swapRows 48]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 4 :=
  ⟨v2.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v2.property⟩
def a1 : List Move := [swapRows 49, swapRows 32]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 :=
  ⟨v2.val.map (movedWord a1.reverse), reflectState _ a1 a1ok v2.property⟩
def a2 : List Move := [swapRows 50]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 4 :=
  ⟨v1.val.map (movedWord a2.reverse), reflectState _ a2 a2ok v1.property⟩
def a3 : List Move := [swapRows 16]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r3 : Closed T 4 :=
  ⟨v3.val.map (movedWord a3.reverse), reflectState _ a3 a3ok v3.property⟩
def r4 : Closed T 4 :=
  ⟨v3.val.map (movedWord a2.reverse), reflectState _ a2 a2ok v3.property⟩
def a4 : List Move := [swapRows 50, swapRows 16]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 :=
  ⟨v3.val.map (movedWord a4.reverse), reflectState _ a4 a4ok v3.property⟩
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w4, w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p5), (usePool p2)] #[r0, r1, v1, r2, v3, r3, r4, r5] ((((((0x10b1119302 : Nat) <<< 64) ||| 0x8a21010740315600) >>> (((h / 8 + (((0xec000a : Nat) >>> ((h % 8) * 3)) &&& 7)) % 26) * 4)) &&& 15))) (by decide +kernel)
def a5 : List Move := [swapRows 32]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 5 :=
  ⟨v4.val.map (movedWord a5.reverse), reflectState _ a5 a5ok v4.property⟩
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r7 : Closed T 5 :=
  ⟨v4.val.map (movedWord a6.reverse), reflectState _ a6 a6ok v4.property⟩
def r8 : Closed T 5 :=
  ⟨v4.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v4.property⟩
def a7 : List Move := [swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 :=
  ⟨v4.val.map (movedWord a7.reverse), reflectState _ a7 a7ok v4.property⟩
def a8 : List Move := [swapRows 49]
theorem a8ok : autoOK T a8 = true := by decide +kernel
def r10 : Closed T 5 :=
  ⟨v4.val.map (movedWord a8.reverse), reflectState _ a8 a8ok v4.property⟩
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p5), (usePool p2)] #[v4, r6, r7, r8, r9, r10] ((((((0x320367108 : Nat) <<< 64) ||| 0x2350104030391) >>> (((h / 8 + (((0x360b0231 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end Prior51812B26

namespace Prior51812B34
def R : List Sig := vars 15
def T : Sig := 0xeae8eae8eae8eae8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) Prior51812B4.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end Prior51812B34

namespace B0
def R : List Sig := vars 7
def T : Sig := 0xe8e8e8e8e8e8e8e8
def P : Nat → Bits
  | 0 => ((0xbecfbecfbecfbecf : BitVec 64) ++ (0xbecfbecfbecfbecf : BitVec 64))
  | 1 => ((0xdf73df73df73df73 : BitVec 64) ++ (0xdf73df73df73df73 : BitVec 64))
  | 2 => ((0xefbcefbcefbcefbc : BitVec 64) ++ (0xefbcefbcefbcefbc : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x4205420542054205 : BitVec 64) ++ (0x4205420542054205 : BitVec 64))
  | 1 => ((0x2412241224122412 : BitVec 64) ++ (0x2412241224122412 : BitVec 64))
  | 2 => ((0x1828182818281828 : BitVec 64) ++ (0x1828182818281828 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 7 P N 0
def w1 := inputObserved 7 P N 1
def w2 := inputObserved 7 P N 2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2]
  (fun _ => ([], [])) (by decide +kernel)
theorem low : Lower true R T 4 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B0

namespace B1
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B1

namespace B2
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B2

namespace B3
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B3

namespace B4
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B4

namespace B5
def R : List Sig := vars 15
def T : Sig := 0xfee8fee8fee8fee8
def P : Nat → Bits
  | 0 => ((0xec33efee19e3bbd8 : BitVec 64) ++ (0x67dfdc33c777b0cf : BitVec 64))
  | 1 => ((0xf4ccf7f6667c3de9 : BitVec 64) ++ (0x99efecccf87bd333 : BitVec 64))
  | 2 => ((0xfb0f3bfb879fc1f6 : BitVec 64) ++ (0x1e77f70f3f83ec3c : BitVec 64))
  | 3 => ((0x3f03dfdf81ffe07 : BitVec 64) ++ (0xe07bfbf03ffc0fc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x20115020a2008840 : BitVec 64) ++ (0x22a0414401108045 : BitVec 64))
  | 1 => ((0x4044884108841080 : BitVec 64) ++ (0x8910821108210112 : BitVec 64))
  | 2 => ((0x810a048050290102 : BitVec 64) ++ (0x140900a052020428 : BitVec 64))
  | 3 => ((0x2a0030005522005 : BitVec 64) ++ (0x4006000aa4400a80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B2.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v0 a0 a0ok
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p3 : Pool R T := prefixPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
def w8 := combineObserved 1 w0 w1
def w9 := combineObserved 1 w8 w2
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w9, w3]
  (fun _ => ([(usePool p0), (joinPools p3 p4)], [])) (by decide +kernel)
def w10 := combineObserved 2 w8 w3
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w10, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := prefixPool s3 [] (by decide +kernel)
def a1 : List Move := [swapRows 50]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v3 a1 a1ok
def r2 : Closed T 4 := rotateClosed v2 a1 a1ok
def a2 : List Move := [swapRows 48]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r3 : Closed T 4 := rotateClosed v1 a2 a2ok
def a3 : List Move := [swapRows 49]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 4 := rotateClosed v1 a3 a3ok
def a4 : List Move := [swapRows 50, swapRows 32]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 := rotateClosed v1 a4 a4ok
def a5 : List Move := [swapRows 50, swapRows 33]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 4 := rotateClosed v1 a5 a5ok
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w8, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v3, r1, v2, r2, r3, r4, r5, r6] ((((((0x3010054b961 : Nat) <<< 64) ||| 0xa20003000071280) >>> (((h / 8 + (((0x9e2031001 : Nat) >>> ((h % 8) * 5)) &&& 31)) % 27) * 4)) &&& 15))) (by decide +kernel)
def r7 : Closed T 5 := rotateClosed v4 a0 a0ok
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r8 : Closed T 5 := rotateClosed v4 a6 a6ok
def a7 : List Move := [swapRows 33, swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 := rotateClosed v4 a7 a7ok
def r10 : Closed T 5 := rotateClosed v4 a2 a2ok
def r11 : Closed T 5 := rotateClosed v4 a3 a3ok
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v4, r7, r8, r9, r10, r11] ((((((0x13934200 : Nat) <<< 64) ||| 0x1316710020080035) >>> (((h / 8 + (((0x40b1830 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B5

namespace B10
def R : List Sig := vars 15
def T : Sig := 0xa880a880a880a880
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 1) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 6, 7)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B3.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 6, 7)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B10

namespace B13
def R : List Sig := vars 15
def T : Sig := 0xeaa8eaa8eaa8eaa8
def P : Nat → Bits
  | 0 => ((0xf7f7fffe3fffffc7 : BitVec 64) ++ (0xf7f7fffe3fffffc7 : BitVec 64))
  | 1 => ((0xb9f8e73fc7743579 : BitVec 64) ++ (0xb9f8e73fc7743579 : BitVec 64))
  | 2 => ((0xdaff07cff878c9ba : BitVec 64) ++ (0xdaff07cff878c9ba : BitVec 64))
  | 3 => ((0xecfff80fff830e3c : BitVec 64) ++ (0xecfff80fff830e3c : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x810000009100007 : BitVec 64) ++ (0x810000009100007 : BitVec 64))
  | 1 => ((0x46264a4642217558 : BitVec 64) ++ (0x46264a4642217558 : BitVec 64))
  | 2 => ((0x2542d41a9042d9a8 : BitVec 64) ++ (0x2542d41a9042d9a8 : BitVec 64))
  | 3 => ((0x138486ad2403ae30 : BitVec 64) ++ (0x138486ad2403ae30 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 1 w4 w3
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2, w5]
  (fun _ => ([], [])) (by decide +kernel)
def w6 := combineObserved 0 w0 w3
def w7 := combineObserved 3 w6 w1
def v1 : Closed T 3 := closeState (raw := R) properPN 3 [w7, w0, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w8 := combineObserved 1 w0 w2
def w9 := combineObserved 0 w8 w1
def v2 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w9, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w10 := combineObserved 1 w0 w1
def w11 := combineObserved 2 w10 w3
def v3 : Closed T 3 := closeState (raw := R) properPN 3 [w11, w0, w1, w2]
  (fun _ => ([], [])) (by decide +kernel)
def w12 := combineObserved 0 w1 w2
def w13 := combineObserved 1 w1 w2
def v4 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w12, w13, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w14 := combineObserved 2 w1 w2
def w15 := combineObserved 1 w14 w3
def v5 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2, w15]
  (fun _ => ([], [])) (by decide +kernel)
def w16 := combineObserved 2 w3 w2
def w17 := combineObserved 3 w16 w1
def v6 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w17, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def a0 : List Move := [swapRows 49]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v1 a0 a0ok
def a1 : List Move := [swapRows 50, swapRows 33]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 3 := rotateClosed v1 a1 a1ok
def a2 : List Move := [swapRows 50]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 3 := rotateClosed v0 a2 a2ok
def v7 : Closed T 4 := closeState (raw := R) properPN 4 [w4, w0, w1, w2, w3]
  (fun h => chooseRoute #[] #[r0, r1, v0, r2] ((((0xd08 : Nat) >>> ((h % 13) * 2)) &&& 3))) (by decide +kernel)
def r3 : Closed T 3 := rotateClosed v3 a2 a2ok
def a3 : List Move := [swapRows 33]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 3 := rotateClosed v2 a3 a3ok
def a4 : List Move := [swapRows 50, swapRows 49]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 3 := rotateClosed v2 a4 a4ok
def v8 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w10, w2, w3]
  (fun h => chooseRoute #[] #[v3, r3, r4, r5] ((((0x20043 : Nat) >>> ((h % 10) * 2)) &&& 3))) (by decide +kernel)
def w18 := combineObserved 2 w0 w3
def v9 : Closed T 4 := closeState (raw := R) properPN 4 [w18, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w19 := combineObserved 3 w0 w1
def v10 : Closed T 4 := closeState (raw := R) properPN 4 [w19, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def v11 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w12, w1, w2, w3]
  (fun _ => ([], [v4])) (by decide +kernel)
def v12 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w13, w3]
  (fun _ => ([], [v4])) (by decide +kernel)
def w20 := combineObserved 2 w1 w3
def r6 : Closed T 3 := rotateClosed v6 a1 a1ok
def r7 : Closed T 3 := rotateClosed v5 a2 a2ok
def v13 : Closed T 4 := closeState (raw := R) properPN 4 [w20, w0, w1, w2, w3]
  (fun _ => ([], [r6, r7])) (by decide +kernel)
def r8 : Closed T 4 := rotateClosed v9 a0 a0ok
def r9 : Closed T 4 := rotateClosed v9 a2 a2ok
def r10 : Closed T 4 := rotateClosed v13 a3 a3ok
def r11 : Closed T 4 := rotateClosed v13 a0 a0ok
def r12 : Closed T 4 := rotateClosed v13 a2 a2ok
def r13 : Closed T 4 := rotateClosed v13 a1 a1ok
def r14 : Closed T 4 := rotateClosed v13 a4 a4ok
def r15 : Closed T 4 := rotateClosed v10 a3 a3ok
def r16 : Closed T 4 := rotateClosed v10 a0 a0ok
def r17 : Closed T 4 := rotateClosed v7 a3 a3ok
def r18 : Closed T 4 := rotateClosed v7 a0 a0ok
def r19 : Closed T 4 := rotateClosed v11 a0 a0ok
def r20 : Closed T 4 := rotateClosed v11 a2 a2ok
def r21 : Closed T 4 := rotateClosed v8 a3 a3ok
def r22 : Closed T 4 := rotateClosed v8 a0 a0ok
def r23 : Closed T 4 := rotateClosed v12 a0 a0ok
def r24 : Closed T 4 := rotateClosed v12 a2 a2ok
def v14 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[] #[v9, r8, r9, v13, r10, r11, r12, r13, r14, v10, r15, r16, v7, r17, r18, v11, r19, r20, v8, r21, r22, v12, r23, r24] ((((((((0x8 : Nat) <<< 64) ||| 0xe80500c55ab70460) <<< 64) ||| 0x96966e0c96f19006) >>> (((h / 8 + (((0x2300d101 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 27) * 5)) &&& 31))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v14 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B13

namespace B14
def R : List Sig := vars 11
def T : Sig := 0xaa88aa88aa88aa88
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xff00ff00ff00ff00, 1, 9)] (by decide +kernel)
end B14

namespace B15
def R : List Sig := vars 11
def T : Sig := 0xeecceecceecceecc
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 8, 9), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 1, 9)] (by decide +kernel)
end B15

namespace B16
def R : List Sig := vars 15
def T : Sig := 0xeac8eac8eac8eac8
theorem low : Lower true R T 4 := by
  exact lower_cubes_two (u := true) (j := 2) (r := 2) (s := 6) (L := 2)
    (z0 := 4) (o0 := 0) (z1 := 0) (o1 := 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide)) (proper_of _ (by decide)) (proper_of _ (by decide))
    (lower_weaken B14.low (by decide))
    (lower_weaken B15.low (by decide))
end B16

namespace B24
def R : List Sig := vars 15
def T : Sig := 0xe888e888e888e888
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 5, 13)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 5, 13)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B24

namespace B38
def R : List Sig := vars 15
def T : Sig := 0xfeeafeeafeeafeea
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B3.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B38

namespace B51
def R : List Sig := vars 63
def T : Sig := 0xfee8e8a8fc80c080
theorem s0 : Slice true R T 0x4444444444444444 5 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B8.low
theorem s1 : Slice true R T 0x2222222222222222 5 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 66, swapRows 67] ++ fixRows 2 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s2 : Slice true R T 0x5050505050505050 5 :=
  slice_correct (ms := [swapRows 64, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B8.low
theorem s3 : Slice true R T 0xa0a0a0a0a0a0a0a 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 4 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s4 : Slice true R T 0xaa00aa00aa00aa00 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 0 9) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s6 : Slice true R T 0xaaaa0000aaaa0000 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 0 17) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s8 : Slice true R T 0x5555555500000000 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67] ++ fixRows 1 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s9 : Slice true R T 0xaaaaaaaa 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67] ++ fixRows 32 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s10 : Slice true R T 0x3300330033003300 5 :=
  slice_correct (ms := [swapRows 32, swapRows 65, swapRows 83] ++ fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s11 : Slice true R T 0xcc00cc00cc00cc 5 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 83, swapRows 84] ++ fixRows 8 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B8.low
theorem s12 : Slice true R T 0x3333000033330000 5 :=
  slice_correct (ms := [swapRows 32, swapRows 65, swapRows 67, swapRows 84] ++ fixRows 2 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s13 : Slice true R T 0xcccc0000cccc 4 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 16 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
theorem s14 : Slice true R T 0xcccc0000cccc0000 5 :=
  slice_correct (ms := [swapRows 16, swapRows 65, swapRows 67, swapRows 84] ++ fixRows 0 18) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s15 : Slice true R T 0x3333333300000000 5 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67] ++ fixRows 2 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s16 : Slice true R T 0xcccccccc 4 :=
  slice_correct (ms := [swapRows 32, swapRows 65, swapRows 66, swapRows 67] ++ fixRows 32 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
theorem s17 : Slice true R T 0xcccccccc00000000 5 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67] ++ fixRows 0 34) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s18 : Slice true R T 0xf000f000f000f00 5 :=
  slice_correct (ms := [swapRows 32, swapRows 33, swapRows 66, swapRows 83] ++ fixRows 4 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s19 : Slice true R T 0xf000f000f000f0 5 :=
  slice_correct (ms := [swapRows 66, swapRows 83, swapRows 84] ++ fixRows 8 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B8.low
theorem s20 : Slice true R T 0xf0f00000f0f0000 5 :=
  slice_correct (ms := [swapRows 32, swapRows 33, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 4 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s21 : Slice true R T 0xf0f00000f0f0 4 :=
  slice_correct (ms := [swapRows 66, swapRows 67, swapRows 84] ++ fixRows 16 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
theorem s22 : Slice true R T 0xf0f00000f0f00000 5 :=
  slice_correct (ms := [swapRows 16, swapRows 33, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 0 20) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s23 : Slice true R T 0xf0f0f0f00000000 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67] ++ fixRows 4 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s24 : Slice true R T 0xf0f0f0f0 4 :=
  slice_correct (ms := [swapRows 32, swapRows 66, swapRows 67] ++ fixRows 32 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
theorem s25 : Slice true R T 0xf0f0f0f000000000 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67] ++ fixRows 0 36) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s26 : Slice true R T 0xff000000ff 5 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 24 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
theorem s27 : Slice true R T 0xff000000ff0000 7 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s28 : Slice true R T 0xff000000ff00 5 :=
  slice_correct (ms := [swapRows 32, swapRows 33, swapRows 67, swapRows 84] ++ fixRows 16 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s29 : Slice true R T 0xff00ff00000000 5 :=
  slice_correct (ms := [swapRows 67] ++ fixRows 8 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B8.low
theorem s30 : Slice true R T 0xff00ff0000000000 7 :=
  slice_correct (ms := [swapRows 67] ++ fixRows 0 40) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s31 : Slice true R T 0xffff 3 :=
  slice_correct (ms := [swapRows 32, swapRows 33, swapRows 67] ++ fixRows 48 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B0.low
theorem s34 : Slice true R T 0xffff000000000000 7 :=
  slice_correct (ms := fixRows 0 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s40 : Slice true R T 0x2200220022002200 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 50, swapRows 83] ++ fixRows 2 9) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s43 : Slice true R T 0x2222000022220000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 2 17) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s48 : Slice true R T 0x4444444400000000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 50, swapRows 67] ++ fixRows 1 34) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s53 : Slice true R T 0xa000a000a000a00 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66, swapRows 83, swapRows 84] ++ fixRows 4 9) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s56 : Slice true R T 0xa0a00000a0a0000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66, swapRows 84] ++ fixRows 4 17) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s61 : Slice true R T 0x5050505000000000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66] ++ fixRows 1 36) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s66 : Slice true R T 0xaa000000aa 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 24 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s71 : Slice true R T 0x55005500 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 33 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s98 : Slice true R T 0xcc000000cc0000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 8 18) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s100 : Slice true R T 0x3300330000000000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67] ++ fixRows 2 40) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s103 : Slice true R T 0x3333000000000000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50] ++ fixRows 2 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s113 : Slice true R T 0xf0000000f00000 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67, swapRows 84] ++ fixRows 8 20) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s115 : Slice true R T 0xf000f0000000000 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67] ++ fixRows 4 40) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s118 : Slice true R T 0xf0f000000000000 4 :=
  slice_correct (ms := [swapRows 50] ++ fixRows 4 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s138 : Slice true R T 0x8844884488448844 6 :=
  slice_correct (ms := [swapRows 80, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 0 2 ++ [(0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s140 : Slice true R T 0xa050a050a050a050 6 :=
  slice_correct (ms := [swapRows 80, swapRows 66, swapRows 83] ++ fixRows 0 4 ++ [(0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s142 : Slice true R T 0xaa550000aa550000 6 :=
  slice_correct (ms := [swapRows 80, swapRows 83] ++ fixRows 0 16 ++ [(0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s144 : Slice true R T 0xaa55aa5500000000 6 :=
  slice_correct (ms := [swapRows 80, swapRows 83, swapRows 84] ++ fixRows 0 32 ++ [(0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s151 : Slice true R T 0xaaaa5555 7 :=
  slice_correct (ms := [swapRows 80, swapRows 81, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 32 0 ++ [(0x5555000055550000, 0xaaaa0000aaaa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s152 : Slice true R T 0xaaaa555500000000 6 :=
  slice_correct (ms := [swapRows 80, swapRows 84] ++ fixRows 0 32 ++ [(0x5555000055550000, 0xaaaa0000aaaa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s155 : Slice true R T 0xaa00aa0055005500 7 :=
  slice_correct (ms := [swapRows 80, swapRows 81, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 0 8 ++ [(0x5555555500000000, 0xaaaaaaaa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s160 : Slice true R T 0xc3c30000c3c30000 6 :=
  slice_correct (ms := [swapRows 16, swapRows 81, swapRows 82, swapRows 83] ++ fixRows 0 16 ++ [(0x3030303030303030, 0xc0c0c0c0c0c0c0c, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s161 : Slice true R T 0xc3c3c3c300000000 6 :=
  slice_correct (ms := [swapRows 16, swapRows 81, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 0 32 ++ [(0x3030303030303030, 0xc0c0c0c0c0c0c0c, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s170 : Slice true R T 0xcc003300cc0033 7 :=
  slice_correct (ms := [swapRows 81, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 8 0 ++ [(0x3333000033330000, 0xcccc0000cccc, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s173 : Slice true R T 0x4444444411111111 7 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 66, swapRows 83] ++ fixRows 1 0 ++ [(0x3333333300000000, 0xcccccccc, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s175 : Slice true R T 0xc0c0c0c030303030 5 :=
  slice_correct (ms := [swapRows 48, swapRows 81, swapRows 66, swapRows 83] ++ fixRows 0 4 ++ [(0x3333333300000000, 0xcccccccc, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B34.low
theorem s180 : Slice true R T 0xa00aa00aa00aa00a 5 :=
  slice_correct (ms := [swapRows 64, swapRows 82, swapRows 67] ++ fixRows 0 1 ++ [(0xf000f000f000f00, 0xf000f000f000f0, 4)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B34.low
theorem s188 : Slice true R T 0xf0000f00f0000f 7 :=
  slice_correct (ms := [swapRows 82, swapRows 67, swapRows 84] ++ fixRows 8 0 ++ [(0xf0f00000f0f0000, 0xf0f00000f0f0, 4)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s191 : Slice true R T 0x5050505005050505 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 1 0 ++ [(0xf0f0f0f00000000, 0xf0f0f0f0, 4)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s198 : Slice true R T 0xaa0000aaaa0000aa 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 0 1 ++ [(0xff000000ff0000, 0xff000000ff00, 8)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s209 : Slice true R T 0xff00000000ff 7 :=
  slice_correct (ms := [swapRows 83] ++ fixRows 16 0 ++ [(0xff00ff00000000, 0xff00ff00, 8)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
theorem s210 : Slice true R T 0xff00000000ff0000 6 :=
  slice_correct (ms := [swapRows 16, swapRows 33, swapRows 50, swapRows 83] ++ fixRows 0 16 ++ [(0xff00ff00000000, 0xff00ff00, 8)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s211 : Slice true R T 0x5555000000005555 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 1 0 ++ [(0xffff00000000, 0xffff0000, 16)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior51812B26.low
def Pos : Nat → Bits
  | 0 => ((0xff34f0e72d51fcd : BitVec 64) ++ (0xff34f0e72d51fcd : BitVec 64))
  | 1 => ((0x963de9bdca68ebdf : BitVec 64) ++ (0x963de9bdca68ebdf : BitVec 64))
  | 2 => ((0xf392faeb2dbf5cbb : BitVec 64) ++ (0xf392faeb2dbf5cbb : BitVec 64))
  | 3 => ((0xf97e9571f567e6f2 : BitVec 64) ++ (0xf97e9571f567e6f2 : BitVec 64))
  | 4 => ((0xf9ccbdd69d5eaf25 : BitVec 64) ++ (0xf9ccbdd69d5eaf25 : BitVec 64))
  | 5 => ((0xceeb36d77bb93146 : BitVec 64) ++ (0xceeb36d77bb93146 : BitVec 64))
  | _ => 0
def Neg : Nat → Bits
  | 0 => ((0x2db3470230c40fcd : BitVec 64) ++ (0x2db3470230c40fcd : BitVec 64))
  | 1 => ((0x8618e83cca688353 : BitVec 64) ++ (0x8618e83cca688353 : BitVec 64))
  | 2 => ((0x382aae9011b5caa : BitVec 64) ++ (0x382aae9011b5caa : BitVec 64))
  | 3 => ((0xb87e1141f46764d0 : BitVec 64) ++ (0xb87e1141f46764d0 : BitVec 64))
  | 4 => ((0x71c4bd961d14ab25 : BitVec 64) ++ (0x71c4bd961d14ab25 : BitVec 64))
  | 5 => ((0xca6914d76bb93006 : BitVec 64) ++ (0xca6914d76bb93006 : BitVec 64))
  | _ => 0
theorem correctPairs : properPairs T (asRow Pos) (asRow Neg) := by unfold properPairs; decide +kernel
def auto1 : List Move := [swapRows 33]
theorem auto1ok : autoOK T auto1 = true := by decide +kernel
def auto2 : List Move := [swapRows 48, swapRows 84]
theorem auto2ok : autoOK T auto2 = true := by decide +kernel
def auto3 : List Move := [swapRows 48, swapRows 33, swapRows 84]
theorem auto3ok : autoOK T auto3 = true := by decide +kernel
def w0 := inputObserved 63 Pos Neg 0
def w1 := inputObserved 63 Pos Neg 1
def w2 := inputObserved 63 Pos Neg 2
def w3 := inputObserved 63 Pos Neg 3
def w4 := inputObserved 63 Pos Neg 4
def w5 := inputObserved 63 Pos Neg 5
def w6 := combineObserved 0 w1 w2
def w7 := combineObserved 0 w0 w1
def w8 := combineObserved 1 w7 w2
def w9 := combineObserved 1 w1 w8
def w10 := combineObserved 0 w0 w2
def w11 := combineObserved 1 w10 w1
def w12 := combineObserved 2 w1 w2
def w13 := combineObserved 0 w8 w1
def w14 := combineObserved 0 w1 w4
def w15 := combineObserved 3 w2 w4
def w16 := combineObserved 0 w3 w2
def w17 := combineObserved 3 w16 w1
def w18 := combineObserved 2 w0 w2
def w19 := combineObserved 0 w0 w5
def w20 := combineObserved 0 w3 w1
def w21 := combineObserved 3 w20 w2
def w22 := combineObserved 0 w2 w5
def w23 := combineObserved 3 w2 w5
def w24 := combineObserved 3 w16 w5
def w25 := combineObserved 1 w24 w1
def w26 := combineObserved 3 w10 w4
def w27 := combineObserved 3 w26 w1
def w28 := combineObserved 1 w3 w2
def w29 := combineObserved 3 w16 w28
def w30 := combineObserved 1 w0 w1
def w31 := combineObserved 1 w3 w1
def w32 := combineObserved 3 w20 w31
def w33 := combineObserved 1 w0 w2
def w34 := combineObserved 0 w30 w5
def w35 := combineObserved 3 w16 w9
def w36 := combineObserved 0 w9 w4
def w37 := combineObserved 1 w12 w10
def w38 := combineObserved 3 w1 w2
def w39 := combineObserved 3 w38 w4
def w40 := combineObserved 0 w2 w4
def w41 := combineObserved 3 w22 w1
def w42 := combineObserved 1 w10 w20
def w43 := combineObserved 3 w2 w3
def w44 := combineObserved 1 w43 w7
def w45 := combineObserved 1 w10 w14
def w46 := combineObserved 1 w1 w40
def w47 := combineObserved 0 w3 w4
def w48 := combineObserved 1 w15 w7
def w49 := combineObserved 1 w7 w47
def w50 := combineObserved 0 w49 w2
def w51 := combineObserved 1 w2 w49
def w52 := combineObserved 3 w50 w51
def w53 := combineObserved 1 w16 w19
def w54 := combineObserved 0 w53 w1
def w55 := combineObserved 1 w1 w53
def w56 := combineObserved 1 w20 w19
def w57 := combineObserved 1 w56 w2
def w58 := combineObserved 1 w10 w47
def w59 := combineObserved 3 w58 w1
def w60 := combineObserved 2 w58 w1
def w61 := combineObserved 2 w56 w2
def w62 := combineObserved 2 w1 w47
def w63 := combineObserved 3 w6 w30
def w64 := combineObserved 3 w6 w9
def w65 := combineObserved 2 w30 w5
def w66 := combineObserved 2 w30 w2
def w67 := combineObserved 3 w38 w33
def w68 := combineObserved 0 w11 w2
def w69 := combineObserved 1 w1 w34
def w70 := combineObserved 3 w1 w33
def w71 := combineObserved 0 w33 w5
def w72 := combineObserved 0 w1 w5
def w73 := combineObserved 1 w15 w1
def w74 := combineObserved 0 w1 w28
def w75 := combineObserved 3 w1 w5
def w76 := combineObserved 2 w69 w2
def w77 := combineObserved 1 w34 w2
def w78 := combineObserved 0 w28 w4
def w79 := combineObserved 3 w78 w1
def w80 := combineObserved 1 w71 w1
def w81 := combineObserved 1 w72 w2
def w82 := combineObserved 3 w22 w30
def w83 := combineObserved 3 w75 w33
def w84 := combineObserved 2 w0 w1
def w85 := combineObserved 1 w84 w2
def w86 := combineObserved 1 w18 w1
def w87 := combineObserved 3 w43 w1
def w88 := combineObserved 3 w43 w5
def w89 := combineObserved 1 w88 w1
def w90 := combineObserved 3 w18 w4
def w91 := combineObserved 3 w90 w1
def w92 := combineObserved 3 w1 w3
def w93 := combineObserved 3 w92 w5
def w94 := combineObserved 3 w3 w1
def w95 := combineObserved 1 w84 w43
def w96 := combineObserved 1 w18 w14
def w97 := combineObserved 1 w84 w15
def w98 := combineObserved 3 w1 w4
def w99 := combineObserved 1 w43 w19
def w100 := combineObserved 1 w94 w2
def w101 := combineObserved 3 w3 w2
def w102 := combineObserved 1 w101 w1
def w103 := combineObserved 3 w0 w2
def w104 := combineObserved 3 w103 w1
def w105 := combineObserved 3 w0 w1
def w106 := combineObserved 3 w105 w2
def w107 := combineObserved 3 w103 w5
def w108 := combineObserved 1 w107 w1
def w109 := combineObserved 3 w101 w4
def w110 := combineObserved 3 w109 w1
def w111 := combineObserved 1 w1 w47
def w112 := combineObserved 1 w101 w14
def w113 := combineObserved 2 w1 w40
def w114 := combineObserved 1 w94 w15
def w115 := combineObserved 0 w0 w3
def w116 := combineObserved 1 w0 w3
def w117 := combineObserved 3 w115 w116
def w118 := combineObserved 0 w9 w116
def w119 := combineObserved 0 w6 w116
def w120 := combineObserved 3 w6 w116
def w121 := combineObserved 3 w9 w116
def w122 := combineObserved 0 w2 w116
def w123 := combineObserved 1 w122 w1
def w124 := combineObserved 0 w1 w116
def w125 := combineObserved 3 w2 w116
def w126 := combineObserved 0 w12 w116
def w127 := combineObserved 3 w38 w116
def w128 := combineObserved 1 w124 w2
def w129 := combineObserved 3 w122 w1
def w130 := combineObserved 1 w125 w1
def w131 := combineObserved 3 w125 w1
def w132 := combineObserved 2 w0 w3
def w133 := combineObserved 1 w132 w2
def w134 := combineObserved 0 w133 w1
def w135 := combineObserved 1 w132 w1
def w136 := combineObserved 1 w135 w2
def w137 := combineObserved 2 w135 w2
def w138 := combineObserved 2 w3 w0
def w139 := combineObserved 1 w138 w2
def w140 := combineObserved 3 w139 w1
def w141 := combineObserved 3 w138 w1
def w142 := combineObserved 0 w141 w2
def w143 := combineObserved 3 w138 w2
def w144 := combineObserved 1 w143 w1
def w145 := combineObserved 3 w132 w2
def w146 := combineObserved 3 w145 w1
def w147 := combineObserved 1 w138 w5
def w148 := combineObserved 3 w138 w5
def w149 := combineObserved 1 w148 w1
def w150 := combineObserved 3 w132 w4
def w151 := combineObserved 3 w150 w1
def w152 := combineObserved 1 w132 w6
def w153 := combineObserved 3 w138 w9
def w154 := combineObserved 1 w132 w12
def w155 := combineObserved 1 w132 w14
def w156 := combineObserved 1 w132 w15
def w157 := combineObserved 0 w0 w4
def w158 := combineObserved 1 w0 w4
def w159 := combineObserved 3 w6 w4
def w160 := combineObserved 0 w158 w5
def w161 := combineObserved 0 w6 w158
def w162 := combineObserved 3 w6 w158
def w163 := combineObserved 0 w9 w158
def w164 := combineObserved 3 w9 w158
def w165 := combineObserved 1 w3 w5
def w166 := combineObserved 0 w165 w4
def w167 := combineObserved 2 w158 w5
def w168 := combineObserved 0 w2 w158
def w169 := combineObserved 1 w168 w1
def w170 := combineObserved 0 w1 w158
def w171 := combineObserved 3 w2 w158
def w172 := combineObserved 0 w12 w158
def w173 := combineObserved 3 w38 w158
def w174 := combineObserved 0 w2 w165
def w175 := combineObserved 3 w174 w1
def w176 := combineObserved 1 w171 w1
def w177 := combineObserved 3 w2 w165
def w178 := combineObserved 3 w177 w1
def w179 := combineObserved 2 w0 w4
def w180 := combineObserved 1 w179 w3
def w181 := combineObserved 2 w3 w5
def w182 := combineObserved 3 w181 w0
def w183 := combineObserved 1 w181 w2
def w184 := combineObserved 0 w183 w1
def w185 := combineObserved 1 w181 w1
def w186 := combineObserved 1 w185 w2
def w187 := combineObserved 2 w185 w2
def w188 := combineObserved 1 w179 w2
def w189 := combineObserved 3 w188 w1
def w190 := combineObserved 3 w179 w1
def w191 := combineObserved 0 w190 w2
def w192 := combineObserved 3 w179 w2
def w193 := combineObserved 1 w192 w1
def w194 := combineObserved 3 w181 w2
def w195 := combineObserved 3 w194 w1
def w196 := combineObserved 1 w181 w6
def w197 := combineObserved 3 w179 w9
def w198 := combineObserved 0 w9 w5
def w199 := combineObserved 1 w181 w12
def w200 := combineObserved 3 w3 w5
def w201 := combineObserved 1 w200 w2
def w202 := combineObserved 0 w201 w1
def w203 := combineObserved 1 w200 w1
def w204 := combineObserved 1 w203 w2
def w205 := combineObserved 2 w203 w2
def w206 := combineObserved 3 w0 w4
def w207 := combineObserved 1 w206 w2
def w208 := combineObserved 3 w207 w1
def w209 := combineObserved 3 w206 w1
def w210 := combineObserved 0 w209 w2
def w211 := combineObserved 3 w206 w2
def w212 := combineObserved 1 w211 w1
def w213 := combineObserved 1 w209 w2
def w214 := combineObserved 3 w200 w2
def w215 := combineObserved 3 w214 w1
def w216 := combineObserved 3 w206 w5
def w217 := combineObserved 1 w216 w1
def w218 := combineObserved 3 w200 w4
def w219 := combineObserved 3 w218 w1
def w220 := combineObserved 1 w200 w6
def w221 := combineObserved 3 w206 w9
def w222 := combineObserved 0 w9 w3
def w223 := combineObserved 1 w200 w12
def w224 := combineObserved 1 w2 w71
def w225 := combineObserved 0 w1 w224
def w226 := combineObserved 1 w69 w2
def w227 := combineObserved 1 w2 w78
def w228 := combineObserved 3 w227 w1
def w229 := combineObserved 0 w62 w2
def w230 := combineObserved 2 w2 w47
def w231 := combineObserved 1 w230 w1
def w232 := combineObserved 2 w2 w19
def w233 := combineObserved 3 w232 w1
def w234 := combineObserved 3 w19 w9
def w235 := combineObserved 3 w19 w1
def w236 := combineObserved 3 w235 w2
def w237 := combineObserved 1 w1 w22
def w238 := combineObserved 3 w47 w5
def w239 := combineObserved 1 w238 w1
def w240 := combineObserved 3 w19 w4
def w241 := combineObserved 3 w240 w1
def w242 := combineObserved 1 w0 w5
def w243 := combineObserved 0 w6 w242
def w244 := combineObserved 0 w2 w242
def w245 := combineObserved 3 w244 w1
def w246 := combineObserved 0 w1 w242
def w247 := combineObserved 1 w47 w6
def w248 := combineObserved 0 w247 w0
def w249 := combineObserved 3 w247 w0
def w250 := combineObserved 1 w19 w6
def w251 := combineObserved 0 w250 w4
def w252 := combineObserved 3 w247 w5
def w253 := combineObserved 1 w19 w247
def w254 := combineObserved 0 w4 w5
def w255 := combineObserved 3 w47 w250
def w256 := combineObserved 0 w250 w5
def w257 := combineObserved 0 w6 w4
def w258 := combineObserved 1 w19 w257
def w259 := combineObserved 1 w19 w47
def w260 := combineObserved 0 w9 w259
def w261 := combineObserved 3 w6 w259
def w262 := combineObserved 3 w47 w9
def w263 := combineObserved 2 w262 w19
def w264 := combineObserved 1 w12 w47
def w265 := combineObserved 1 w19 w264
def w266 := combineObserved 1 w12 w19
def w267 := combineObserved 3 w38 w259
def w268 := combineObserved 1 w19 w14
def w269 := combineObserved 3 w47 w237
def w270 := combineObserved 1 w14 w2
def w271 := combineObserved 1 w113 w19
def w272 := combineObserved 1 w15 w19
def w273 := combineObserved 3 w15 w1
def w274 := combineObserved 1 w19 w273
def w275 := combineObserved 3 w22 w4
def w276 := combineObserved 0 w2 w259
def w277 := combineObserved 1 w276 w1
def w278 := combineObserved 1 w2 w259
def w279 := combineObserved 0 w1 w259
def w280 := combineObserved 1 w279 w2
def w281 := combineObserved 3 w276 w1
def w282 := combineObserved 3 w276 w278
def w283 := combineObserved 1 w1 w259
def w284 := combineObserved 0 w2 w283
def w285 := combineObserved 0 w1 w278
def w286 := combineObserved 3 w2 w283
def w287 := combineObserved 2 w1 w259
def w288 := combineObserved 3 w1 w259
def w289 := combineObserved 3 w2 w259
def w290 := combineObserved 3 w6 w5
def w291 := combineObserved 3 w290 w242
def w292 := combineObserved 1 w3 w4
def w293 := combineObserved 0 w6 w292
def w294 := combineObserved 3 w6 w292
def w295 := combineObserved 0 w9 w292
def w296 := combineObserved 3 w38 w292
def w297 := combineObserved 0 w2 w292
def w298 := combineObserved 1 w297 w1
def w299 := combineObserved 0 w1 w292
def w300 := combineObserved 3 w2 w292
def w301 := combineObserved 1 w300 w1
def w302 := combineObserved 3 w2 w242
def w303 := combineObserved 3 w302 w1
def w304 := combineObserved 2 w3 w4
def w305 := combineObserved 1 w304 w1
def w306 := combineObserved 2 w0 w5
def w307 := combineObserved 1 w306 w2
def w308 := combineObserved 0 w307 w1
def w309 := combineObserved 1 w306 w1
def w310 := combineObserved 1 w309 w2
def w311 := combineObserved 2 w309 w2
def w312 := combineObserved 1 w304 w2
def w313 := combineObserved 3 w312 w1
def w314 := combineObserved 3 w304 w1
def w315 := combineObserved 0 w314 w2
def w316 := combineObserved 3 w304 w2
def w317 := combineObserved 1 w316 w1
def w318 := combineObserved 3 w306 w2
def w319 := combineObserved 3 w318 w1
def w320 := combineObserved 1 w306 w6
def w321 := combineObserved 0 w6 w5
def w322 := combineObserved 3 w304 w9
def w323 := combineObserved 1 w306 w12
def w324 := combineObserved 1 w304 w14
def w325 := combineObserved 3 w3 w4
def w326 := combineObserved 0 w0 w6
def w327 := combineObserved 1 w326 w3
def w328 := combineObserved 0 w3 w6
def w329 := combineObserved 3 w328 w0
def w330 := combineObserved 1 w328 w5
def w331 := combineObserved 3 w328 w5
def w332 := combineObserved 1 w326 w5
def w333 := combineObserved 3 w328 w4
def w334 := combineObserved 1 w3 w6
def w335 := combineObserved 3 w328 w334
def w336 := combineObserved 3 w328 w9
def w337 := combineObserved 1 w0 w6
def w338 := combineObserved 0 w0 w9
def w339 := combineObserved 0 w337 w9
def w340 := combineObserved 2 w337 w5
def w341 := combineObserved 3 w3 w6
def w342 := combineObserved 2 w3 w6
def w343 := combineObserved 2 w0 w6
def w344 := combineObserved 3 w0 w6
def w345 := combineObserved 3 w344 w9
def w346 := combineObserved 1 w6 w5
def w347 := combineObserved 3 w321 w346
def w348 := combineObserved 1 w6 w4
def w349 := combineObserved 0 w0 w346
def w350 := combineObserved 3 w3 w348
def w351 := combineObserved 2 w6 w4
def w352 := combineObserved 3 w351 w1
def w353 := combineObserved 1 w351 w5
def w354 := combineObserved 3 w351 w5
def w355 := combineObserved 2 w6 w5
def w356 := combineObserved 3 w355 w4
def w357 := combineObserved 3 w351 w9
def w358 := combineObserved 3 w23 w1
def w359 := combineObserved 2 w1 w5
def w360 := combineObserved 3 w5 w4
def w361 := combineObserved 3 w222 w5
def w362 := combineObserved 1 w0 w9
def w363 := combineObserved 3 w6 w362
def w364 := combineObserved 1 w3 w9
def w365 := combineObserved 0 w364 w0
def w366 := combineObserved 2 w362 w3
def w367 := combineObserved 0 w362 w4
def w368 := combineObserved 2 w364 w5
def w369 := combineObserved 0 w362 w5
def w370 := combineObserved 2 w362 w5
def w371 := combineObserved 2 w0 w9
def w372 := combineObserved 1 w371 w6
def w373 := combineObserved 3 w3 w9
def w374 := combineObserved 2 w3 w9
def w375 := combineObserved 0 w36 w5
def w376 := combineObserved 1 w9 w4
def w377 := combineObserved 0 w0 w376
def w378 := combineObserved 1 w9 w5
def w379 := combineObserved 3 w3 w378
def w380 := combineObserved 3 w6 w376
def w381 := combineObserved 0 w0 w378
def w382 := combineObserved 3 w3 w376
def w383 := combineObserved 0 w378 w4
def w384 := combineObserved 2 w376 w5
def w385 := combineObserved 2 w9 w5
def w386 := combineObserved 3 w9 w5
def w387 := combineObserved 3 w9 w4
def w388 := combineObserved 1 w4 w5
def w389 := combineObserved 0 w9 w388
def w390 := combineObserved 3 w9 w388
def w391 := combineObserved 1 w1 w5
def w392 := combineObserved 0 w0 w391
def w393 := combineObserved 1 w1 w4
def w394 := combineObserved 3 w3 w393
def w395 := combineObserved 3 w6 w393
def w396 := combineObserved 1 w359 w2
def w397 := combineObserved 1 w15 w6
def w398 := combineObserved 0 w6 w388
def w399 := combineObserved 3 w6 w388
def w400 := combineObserved 0 w2 w388
def w401 := combineObserved 1 w400 w1
def w402 := combineObserved 0 w1 w388
def w403 := combineObserved 3 w2 w388
def w404 := combineObserved 1 w360 w6
def w405 := combineObserved 3 w4 w5
def w406 := combineObserved 3 w405 w6
def w407 := combineObserved 3 w222 w364
def w408 := combineObserved 0 w362 w3
def w409 := combineObserved 3 w22 w9
def w410 := combineObserved 0 w14 w5
def w411 := combineObserved 1 w2 w4
def w412 := combineObserved 0 w1 w411
def w413 := combineObserved 3 w2 w393
def w414 := combineObserved 2 w2 w4
def w415 := combineObserved 3 w414 w9
def w416 := combineObserved 1 w98 w2
def w417 := combineObserved 3 w198 w378
def w418 := combineObserved 0 w376 w5
def w419 := combineObserved 1 w360 w9
def w420 := combineObserved 3 w405 w9
def w421 := combineObserved 0 w38 w0
def w422 := combineObserved 1 w38 w0
def w423 := combineObserved 3 w421 w422
def w424 := combineObserved 0 w12 w0
def w425 := combineObserved 1 w12 w0
def w426 := combineObserved 2 w12 w0
def w427 := combineObserved 1 w426 w5
def w428 := combineObserved 3 w426 w5
def w429 := combineObserved 2 w12 w3
def w430 := combineObserved 3 w12 w3
def w431 := combineObserved 3 w12 w0
def w432 := combineObserved 0 w12 w4
def w433 := combineObserved 0 w38 w4
def w434 := combineObserved 1 w38 w4
def w435 := combineObserved 3 w433 w434
def w436 := combineObserved 1 w12 w4
def w437 := combineObserved 2 w12 w4
def w438 := combineObserved 1 w437 w3
def w439 := combineObserved 2 w12 w5
def w440 := combineObserved 3 w439 w0
def w441 := combineObserved 3 w12 w5
def w442 := combineObserved 3 w38 w5
def w443 := combineObserved 3 w12 w4
def w444 := combineObserved 3 w351 w2
def w445 := combineObserved 0 w2 w254
def w446 := combineObserved 3 w1 w376
def w447 := combineObserved 1 w2 w5
def w448 := combineObserved 0 w0 w447
def w449 := combineObserved 0 w12 w388
def w450 := combineObserved 3 w38 w388
def w451 := combineObserved 1 w360 w12
def w452 := combineObserved 3 w405 w12
def w453 := combineObserved 2 w0 w40
def w454 := combineObserved 0 w270 w5
def w455 := combineObserved 3 w14 w2
def w456 := combineObserved 3 w455 w5
def w457 := combineObserved 1 w14 w3
def w458 := combineObserved 1 w445 w1
def w459 := combineObserved 3 w445 w1
def w460 := combineObserved 1 w275 w1
def w461 := combineObserved 3 w40 w5
def w462 := combineObserved 3 w461 w1
def w463 := combineObserved 1 w40 w72
def w464 := combineObserved 1 w14 w22
def w465 := combineObserved 1 w23 w14
def w466 := combineObserved 2 w2 w5
def w467 := combineObserved 1 w466 w1
def w468 := combineObserved 3 w15 w0
def w469 := combineObserved 0 w15 w5
def w470 := combineObserved 1 w469 w1
def w471 := combineObserved 3 w469 w1
def w472 := combineObserved 3 w23 w4
def w473 := combineObserved 1 w472 w1
def w474 := combineObserved 3 w15 w5
def w475 := combineObserved 3 w474 w1
def w476 := combineObserved 3 w75 w4
def w477 := combineObserved 1 w98 w23
def w478 := combineObserved 3 w400 w1
def w479 := combineObserved 1 w403 w1
def w480 := combineObserved 3 w403 w1
def w481 := combineObserved 1 w360 w2
def w482 := combineObserved 0 w481 w1
def w483 := combineObserved 1 w360 w1
def w484 := combineObserved 2 w483 w2
def w485 := combineObserved 3 w405 w2
def w486 := combineObserved 1 w485 w1
def w487 := combineObserved 3 w360 w2
def w488 := combineObserved 3 w487 w1
def w489 := combineObserved 3 w405 w1
def x0 : Sig := 0xf0f0f0f0f0f0f0f0
def x1 : Sig := 0xffffffff00000000
def x2 : Sig := 0xff00ff00ff00ff00
def x3 : Sig := 0xffff0000ffff0000
def x4 : Sig := 0xcccccccccccccccc
def x5 : Sig := 0xc0c0c0c0c0c0c0c0
def x6 : Sig := 0xcccc0000cccc0000
def x7 : Sig := 0xcccccccc00000000
def x8 : Sig := 0xf0f00000f0f00000
def x9 : Sig := 0xf0f0f0f000000000
def x10 : Sig := 0xfcfcfcfcfcfcfcfc
def x11 : Sig := 0xffffccccffffcccc
def x12 : Sig := 0xffffffffcccccccc
def x13 : Sig := 0xfffffffff0f0f0f0
def x14 : Sig := 0xffffffffffff0000
def x15 : Sig := 0xc0c0c0c0c0c0c0c
def x16 : Sig := 0xcccc0000cccc
def x17 : Sig := 0xffff0000
def x18 : Sig := 0x3030303030303030
def x19 : Sig := 0x3333000033330000
def x20 : Sig := 0xf0f00000f0f0000
def x21 : Sig := 0xf0f0f0f00000000
def x22 : Sig := 0xf000f000f000f000
def x23 : Sig := 0xff00ff00000000
def x24 : Sig := 0xff000000ff000000
def x25 : Sig := 0xf0f00000f0f0
def x26 : Sig := 0x3300330033003300
def x27 : Sig := 0xf000f000f000f00
def x28 : Sig := 0xaaaaaaaaaaaaaaaa
def x29 : Sig := 0x8888888888888888
def x30 : Sig := 0xaaaaaaaa00000000
def x31 : Sig := 0x2222222222222222
def x32 : Sig := 0xa0a0a0a0a0a0a0a
def x33 : Sig := 0xf0f0f0f0
def x34 : Sig := 0x3333333300000000
def x35 : Sig := 0xeeeeeeeeeeeeeeee
def p0 := prefixPool s0 [] (by decide +kernel)
def p1 := prefixPool s0 [(0,x0,x1)] (by decide +kernel)
def p2 := prefixPool s0 [(0,x2,x3),(0,x3,x1)] (by decide +kernel)
def p3 := prefixPool s0 [(0,x3,x1)] (by decide +kernel)
def p4 := prefixPool s1 [] (by decide +kernel)
def p5 := prefixPool s1 [(0,x0,x2)] (by decide +kernel)
def p6 := prefixPool s1 [(0,x2,x3)] (by decide +kernel)
def p7 := prefixPool s2 [] (by decide +kernel)
def p8 := prefixPool s2 [(0,x4,x1)] (by decide +kernel)
def p9 := prefixPool s2 [(0,x2,x3),(0,x3,x1)] (by decide +kernel)
def p10 := prefixPool s2 [(0,x3,x1)] (by decide +kernel)
def p11 := prefixPool s2 [(2,x4,x1)] (by decide +kernel)
def p12 := prefixPool s2 [(2,x3,x1)] (by decide +kernel)
def p13 := prefixPool s3 [] (by decide +kernel)
def p14 := prefixPool s3 [(0,x2,x3)] (by decide +kernel)
def p15 := prefixPool s4 [] (by decide +kernel)
def p16 := prefixPool s4 [(0,x4,x0)] (by decide +kernel)
def p17 := prefixPool s4 [(0,x4,x0),(1,x5,x3)] (by decide +kernel)
def p18 := prefixPool s4 [(0,x4,x0),(1,x5,x1)] (by decide +kernel)
def p19 := prefixPool s4 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p20 := prefixPool s4 [(0,x4,x0),(3,x5,x3)] (by decide +kernel)
def p21 := prefixPool s4 [(0,x4,x0),(3,x5,x1)] (by decide +kernel)
def p22 := prefixPool s4 [(0,x4,x3)] (by decide +kernel)
def p23 := prefixPool s4 [(0,x4,x3),(0,x6,x1)] (by decide +kernel)
def p24 := prefixPool s4 [(0,x4,x3),(1,x6,x0)] (by decide +kernel)
def p25 := prefixPool s4 [(0,x4,x3),(1,x4,x3)] (by decide +kernel)
def p26 := prefixPool s4 [(0,x4,x1)] (by decide +kernel)
def p27 := prefixPool s4 [(0,x4,x1),(1,x7,x0)] (by decide +kernel)
def p28 := prefixPool s4 [(0,x4,x1),(1,x4,x1)] (by decide +kernel)
def p29 := prefixPool s4 [(0,x0,x3)] (by decide +kernel)
def p30 := prefixPool s4 [(0,x0,x3),(0,x8,x1)] (by decide +kernel)
def p31 := prefixPool s4 [(0,x0,x3),(1,x8,x4)] (by decide +kernel)
def p32 := prefixPool s4 [(0,x0,x3),(3,x8,x4)] (by decide +kernel)
def p33 := prefixPool s4 [(0,x0,x1)] (by decide +kernel)
def p34 := prefixPool s4 [(0,x0,x1),(1,x9,x4)] (by decide +kernel)
def p35 := prefixPool s4 [(0,x0,x1),(1,x0,x1)] (by decide +kernel)
def p36 := prefixPool s4 [(0,x0,x1),(3,x9,x4)] (by decide +kernel)
def p37 := prefixPool s4 [(0,x0,x1),(3,x9,x3)] (by decide +kernel)
def p38 := prefixPool s4 [(0,x3,x1)] (by decide +kernel)
def p39 := prefixPool s4 [(0,x3,x1),(1,x3,x1)] (by decide +kernel)
def p40 := prefixPool s4 [(1,x4,x0)] (by decide +kernel)
def p41 := prefixPool s4 [(1,x4,x0),(0,x4,x0),(1,x5,x3)] (by decide +kernel)
def p42 := prefixPool s4 [(1,x4,x0),(0,x4,x0),(1,x5,x1)] (by decide +kernel)
def p43 := prefixPool s4 [(1,x4,x0),(0,x10,x3)] (by decide +kernel)
def p44 := prefixPool s4 [(1,x4,x0),(0,x10,x1)] (by decide +kernel)
def p45 := prefixPool s4 [(1,x4,x0),(1,x10,x3)] (by decide +kernel)
def p46 := prefixPool s4 [(1,x4,x0),(2,x10,x3)] (by decide +kernel)
def p47 := prefixPool s4 [(1,x4,x0),(3,x10,x1)] (by decide +kernel)
def p48 := prefixPool s4 [(1,x4,x3)] (by decide +kernel)
def p49 := prefixPool s4 [(1,x4,x3),(1,x11,x1)] (by decide +kernel)
def p50 := prefixPool s4 [(1,x4,x1)] (by decide +kernel)
def p51 := prefixPool s4 [(1,x4,x1),(0,x12,x0)] (by decide +kernel)
def p52 := prefixPool s4 [(1,x4,x1),(2,x12,x0)] (by decide +kernel)
def p53 := prefixPool s4 [(1,x0,x1)] (by decide +kernel)
def p54 := prefixPool s4 [(1,x0,x1),(2,x13,x4)] (by decide +kernel)
def p55 := prefixPool s4 [(1,x3,x1)] (by decide +kernel)
def p56 := prefixPool s4 [(1,x3,x1),(0,x14,x0)] (by decide +kernel)
def p57 := prefixPool s4 [(1,x3,x1),(2,x14,x4)] (by decide +kernel)
def p58 := prefixPool s4 [(2,x4,x0)] (by decide +kernel)
def p59 := prefixPool s4 [(2,x4,x0),(0,x4,x0)] (by decide +kernel)
def p60 := prefixPool s4 [(2,x4,x0),(1,x15,x3)] (by decide +kernel)
def p61 := prefixPool s4 [(2,x4,x0),(1,x15,x1)] (by decide +kernel)
def p62 := prefixPool s4 [(2,x4,x0),(1,x4,x0)] (by decide +kernel)
def p63 := prefixPool s4 [(2,x4,x0),(1,x4,x1)] (by decide +kernel)
def p64 := prefixPool s4 [(2,x4,x0),(3,x4,x0)] (by decide +kernel)
def p65 := prefixPool s4 [(2,x4,x3)] (by decide +kernel)
def p66 := prefixPool s4 [(2,x4,x3),(2,x16,x1)] (by decide +kernel)
def p67 := prefixPool s4 [(2,x3,x1),(3,x17,x4)] (by decide +kernel)
def p68 := prefixPool s4 [(3,x4,x0)] (by decide +kernel)
def p69 := prefixPool s4 [(3,x4,x0),(1,x0,x1)] (by decide +kernel)
def p70 := prefixPool s4 [(3,x4,x0),(2,x18,x1)] (by decide +kernel)
def p71 := prefixPool s4 [(3,x4,x0),(3,x18,x3)] (by decide +kernel)
def p72 := prefixPool s4 [(3,x4,x0),(3,x18,x1)] (by decide +kernel)
def p73 := prefixPool s4 [(3,x4,x3)] (by decide +kernel)
def p74 := prefixPool s4 [(3,x4,x3),(0,x19,x1),(1,x3,x1)] (by decide +kernel)
def p75 := prefixPool s4 [(3,x4,x3),(1,x3,x1)] (by decide +kernel)
def p76 := prefixPool s4 [(3,x4,x1)] (by decide +kernel)
def p77 := prefixPool s4 [(3,x4,x1),(0,x4,x1)] (by decide +kernel)
def p78 := prefixPool s4 [(3,x4,x1),(1,x0,x1)] (by decide +kernel)
def p79 := prefixPool s4 [(3,x4,x1),(1,x3,x1)] (by decide +kernel)
def p80 := prefixPool s4 [(3,x0,x3)] (by decide +kernel)
def p81 := prefixPool s4 [(3,x0,x3),(1,x20,x4)] (by decide +kernel)
def p82 := prefixPool s4 [(3,x0,x3),(1,x20,x1)] (by decide +kernel)
def p83 := prefixPool s4 [(3,x0,x3),(3,x20,x4)] (by decide +kernel)
def p84 := prefixPool s4 [(3,x0,x1)] (by decide +kernel)
def p85 := prefixPool s4 [(3,x0,x1),(1,x21,x4)] (by decide +kernel)
def p86 := prefixPool s4 [(3,x0,x1),(3,x21,x4)] (by decide +kernel)
def p87 := prefixPool s4 [(3,x3,x1)] (by decide +kernel)
def p88 := prefixPool s6 [] (by decide +kernel)
def p89 := prefixPool s6 [(0,x4,x0)] (by decide +kernel)
def p90 := prefixPool s6 [(0,x4,x0),(1,x5,x2)] (by decide +kernel)
def p91 := prefixPool s6 [(0,x4,x0),(1,x5,x1)] (by decide +kernel)
def p92 := prefixPool s6 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p93 := prefixPool s6 [(0,x4,x0),(1,x4,x0),(1,x2,x1)] (by decide +kernel)
def p94 := prefixPool s6 [(0,x4,x0),(1,x2,x1)] (by decide +kernel)
def p95 := prefixPool s6 [(0,x4,x0),(3,x5,x2)] (by decide +kernel)
def p96 := prefixPool s6 [(0,x4,x0),(3,x5,x1)] (by decide +kernel)
def p97 := prefixPool s6 [(0,x4,x1)] (by decide +kernel)
def p98 := prefixPool s6 [(0,x4,x1),(1,x7,x0)] (by decide +kernel)
def p99 := prefixPool s6 [(0,x0,x2)] (by decide +kernel)
def p100 := prefixPool s6 [(0,x0,x2),(3,x22,x1)] (by decide +kernel)
def p101 := prefixPool s6 [(0,x0,x1)] (by decide +kernel)
def p102 := prefixPool s6 [(0,x0,x1),(1,x9,x4)] (by decide +kernel)
def p103 := prefixPool s6 [(0,x0,x1),(1,x0,x1)] (by decide +kernel)
def p104 := prefixPool s6 [(0,x0,x1),(3,x9,x4)] (by decide +kernel)
def p105 := prefixPool s6 [(1,x4,x0)] (by decide +kernel)
def p106 := prefixPool s6 [(1,x4,x0),(0,x4,x0),(1,x5,x2)] (by decide +kernel)
def p107 := prefixPool s6 [(1,x4,x0),(0,x4,x0),(1,x5,x1)] (by decide +kernel)
def p108 := prefixPool s6 [(1,x4,x0),(0,x10,x1)] (by decide +kernel)
def p109 := prefixPool s6 [(1,x4,x0),(1,x2,x1)] (by decide +kernel)
def p110 := prefixPool s6 [(1,x4,x0),(2,x10,x1)] (by decide +kernel)
def p111 := prefixPool s6 [(1,x4,x0),(3,x10,x1)] (by decide +kernel)
def p112 := prefixPool s6 [(1,x4,x1)] (by decide +kernel)
def p113 := prefixPool s6 [(1,x4,x1),(2,x12,x0)] (by decide +kernel)
def p114 := prefixPool s6 [(1,x0,x1)] (by decide +kernel)
def p115 := prefixPool s6 [(1,x2,x1)] (by decide +kernel)
def p116 := prefixPool s6 [(2,x4,x0)] (by decide +kernel)
def p117 := prefixPool s6 [(2,x4,x0),(1,x15,x2)] (by decide +kernel)
def p118 := prefixPool s6 [(2,x4,x0),(1,x15,x1)] (by decide +kernel)
def p119 := prefixPool s6 [(2,x4,x0),(1,x2,x1)] (by decide +kernel)
def p120 := prefixPool s6 [(2,x4,x0),(2,x15,x1)] (by decide +kernel)
def p121 := prefixPool s6 [(2,x4,x0),(3,x15,x2)] (by decide +kernel)
def p122 := prefixPool s6 [(2,x4,x2)] (by decide +kernel)
def p123 := prefixPool s6 [(2,x4,x1)] (by decide +kernel)
def p124 := prefixPool s6 [(2,x0,x1)] (by decide +kernel)
def p125 := prefixPool s6 [(3,x4,x0)] (by decide +kernel)
def p126 := prefixPool s6 [(3,x4,x0),(0,x18,x1)] (by decide +kernel)
def p127 := prefixPool s6 [(3,x4,x0),(2,x18,x1)] (by decide +kernel)
def p128 := prefixPool s6 [(3,x4,x2)] (by decide +kernel)
def p129 := prefixPool s6 [(3,x4,x2),(1,x2,x1)] (by decide +kernel)
def p130 := prefixPool s6 [(3,x4,x1)] (by decide +kernel)
def p131 := prefixPool s6 [(3,x0,x1)] (by decide +kernel)
def p132 := prefixPool s6 [(3,x0,x1),(1,x21,x4)] (by decide +kernel)
def p133 := prefixPool s6 [(3,x0,x1),(3,x21,x4)] (by decide +kernel)
def p134 := prefixPool s6 [(3,x2,x1)] (by decide +kernel)
def p135 := prefixPool s6 [(3,x2,x1),(1,x23,x4)] (by decide +kernel)
def p136 := prefixPool s8 [] (by decide +kernel)
def p137 := prefixPool s8 [(0,x4,x0)] (by decide +kernel)
def p138 := prefixPool s8 [(0,x4,x0),(0,x5,x3)] (by decide +kernel)
def p139 := prefixPool s8 [(0,x4,x0),(0,x2,x3)] (by decide +kernel)
def p140 := prefixPool s8 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p141 := prefixPool s8 [(0,x4,x0),(1,x4,x0),(0,x10,x2)] (by decide +kernel)
def p142 := prefixPool s8 [(0,x4,x0),(1,x4,x0),(0,x10,x3)] (by decide +kernel)
def p143 := prefixPool s8 [(0,x4,x0),(1,x4,x0),(0,x2,x3)] (by decide +kernel)
def p144 := prefixPool s8 [(0,x4,x0),(2,x5,x3)] (by decide +kernel)
def p145 := prefixPool s8 [(0,x4,x0),(3,x5,x3)] (by decide +kernel)
def p146 := prefixPool s8 [(0,x4,x0),(3,x5,x3),(1,x4,x0)] (by decide +kernel)
def p147 := prefixPool s8 [(0,x4,x2)] (by decide +kernel)
def p148 := prefixPool s8 [(0,x4,x3)] (by decide +kernel)
def p149 := prefixPool s8 [(0,x4,x3),(0,x2,x3)] (by decide +kernel)
def p150 := prefixPool s8 [(0,x4,x3),(1,x6,x0)] (by decide +kernel)
def p151 := prefixPool s8 [(0,x4,x3),(3,x6,x0)] (by decide +kernel)
def p152 := prefixPool s8 [(0,x0,x2)] (by decide +kernel)
def p153 := prefixPool s8 [(0,x0,x2),(3,x22,x4)] (by decide +kernel)
def p154 := prefixPool s8 [(0,x0,x3)] (by decide +kernel)
def p155 := prefixPool s8 [(0,x0,x3),(0,x2,x3)] (by decide +kernel)
def p156 := prefixPool s8 [(0,x0,x3),(1,x8,x4)] (by decide +kernel)
def p157 := prefixPool s8 [(0,x2,x3)] (by decide +kernel)
def p158 := prefixPool s8 [(0,x2,x3),(3,x24,x4)] (by decide +kernel)
def p159 := prefixPool s8 [(1,x4,x0)] (by decide +kernel)
def p160 := prefixPool s8 [(1,x4,x0),(0,x10,x2)] (by decide +kernel)
def p161 := prefixPool s8 [(1,x4,x0),(0,x10,x3)] (by decide +kernel)
def p162 := prefixPool s8 [(1,x4,x0),(0,x2,x3)] (by decide +kernel)
def p163 := prefixPool s8 [(1,x4,x0),(1,x10,x3)] (by decide +kernel)
def p164 := prefixPool s8 [(1,x4,x0),(2,x10,x3)] (by decide +kernel)
def p165 := prefixPool s8 [(1,x4,x0),(3,x10,x2)] (by decide +kernel)
def p166 := prefixPool s8 [(2,x4,x0)] (by decide +kernel)
def p167 := prefixPool s8 [(2,x4,x0),(0,x15,x3)] (by decide +kernel)
def p168 := prefixPool s8 [(2,x4,x0),(0,x4,x0)] (by decide +kernel)
def p169 := prefixPool s8 [(2,x4,x0),(0,x0,x2)] (by decide +kernel)
def p170 := prefixPool s8 [(2,x4,x0),(0,x0,x3)] (by decide +kernel)
def p171 := prefixPool s8 [(2,x4,x0),(0,x2,x3)] (by decide +kernel)
def p172 := prefixPool s8 [(2,x4,x0),(1,x4,x0)] (by decide +kernel)
def p173 := prefixPool s8 [(2,x4,x0),(2,x15,x3)] (by decide +kernel)
def p174 := prefixPool s8 [(2,x4,x0),(3,x4,x0)] (by decide +kernel)
def p175 := prefixPool s8 [(2,x4,x2)] (by decide +kernel)
def p176 := prefixPool s8 [(2,x4,x3)] (by decide +kernel)
def p177 := prefixPool s8 [(2,x4,x3),(0,x2,x3)] (by decide +kernel)
def p178 := prefixPool s8 [(2,x4,x3),(1,x16,x0)] (by decide +kernel)
def p179 := prefixPool s8 [(2,x0,x3)] (by decide +kernel)
def p180 := prefixPool s8 [(2,x0,x3),(1,x25,x4)] (by decide +kernel)
def p181 := prefixPool s8 [(3,x4,x0)] (by decide +kernel)
def p182 := prefixPool s8 [(3,x4,x0),(0,x18,x2)] (by decide +kernel)
def p183 := prefixPool s8 [(3,x4,x0),(0,x4,x2)] (by decide +kernel)
def p184 := prefixPool s8 [(3,x4,x0),(3,x18,x3)] (by decide +kernel)
def p185 := prefixPool s8 [(3,x4,x2)] (by decide +kernel)
def p186 := prefixPool s8 [(3,x4,x2),(0,x26,x3)] (by decide +kernel)
def p187 := prefixPool s8 [(3,x4,x3)] (by decide +kernel)
def p188 := prefixPool s8 [(3,x4,x3),(0,x4,x3)] (by decide +kernel)
def p189 := prefixPool s8 [(3,x4,x3),(3,x19,x0)] (by decide +kernel)
def p190 := prefixPool s8 [(3,x0,x2)] (by decide +kernel)
def p191 := prefixPool s8 [(3,x0,x2),(3,x27,x4)] (by decide +kernel)
def p192 := prefixPool s8 [(3,x0,x3)] (by decide +kernel)
def p193 := prefixPool s8 [(3,x0,x3),(1,x20,x4)] (by decide +kernel)
def p194 := prefixPool s8 [(3,x0,x3),(3,x20,x4)] (by decide +kernel)
def p195 := prefixPool s9 [] (by decide +kernel)
def p196 := prefixPool s10 [] (by decide +kernel)
def p197 := prefixPool s11 [] (by decide +kernel)
def p198 := prefixPool s11 [(0,x0,x3)] (by decide +kernel)
def p199 := prefixPool s12 [] (by decide +kernel)
def p200 := prefixPool s13 [] (by decide +kernel)
def p201 := prefixPool s14 [] (by decide +kernel)
def p202 := prefixPool s15 [] (by decide +kernel)
def p203 := prefixPool s16 [] (by decide +kernel)
def p204 := prefixPool s17 [] (by decide +kernel)
def p205 := prefixPool s18 [] (by decide +kernel)
def p206 := prefixPool s19 [] (by decide +kernel)
def p207 := prefixPool s19 [(0,x4,x3)] (by decide +kernel)
def p208 := prefixPool s20 [] (by decide +kernel)
def p209 := prefixPool s21 [] (by decide +kernel)
def p210 := prefixPool s22 [] (by decide +kernel)
def p211 := prefixPool s23 [] (by decide +kernel)
def p212 := prefixPool s24 [] (by decide +kernel)
def p213 := prefixPool s25 [] (by decide +kernel)
def p214 := prefixPool s26 [] (by decide +kernel)
def p215 := prefixPool s27 [] (by decide +kernel)
def p216 := prefixPool s27 [(0,x28,x4)] (by decide +kernel)
def p217 := prefixPool s27 [(0,x28,x4),(0,x29,x0)] (by decide +kernel)
def p218 := prefixPool s27 [(0,x28,x4),(0,x29,x1)] (by decide +kernel)
def p219 := prefixPool s27 [(0,x28,x4),(3,x29,x0)] (by decide +kernel)
def p220 := prefixPool s27 [(0,x28,x0)] (by decide +kernel)
def p221 := prefixPool s27 [(0,x28,x1)] (by decide +kernel)
def p222 := prefixPool s27 [(0,x28,x1),(0,x4,x0)] (by decide +kernel)
def p223 := prefixPool s27 [(0,x28,x1),(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p224 := prefixPool s27 [(0,x28,x1),(0,x4,x1)] (by decide +kernel)
def p225 := prefixPool s27 [(0,x28,x1),(0,x0,x1)] (by decide +kernel)
def p226 := prefixPool s27 [(0,x28,x1),(1,x30,x4)] (by decide +kernel)
def p227 := prefixPool s27 [(0,x28,x1),(1,x30,x0)] (by decide +kernel)
def p228 := prefixPool s27 [(0,x28,x1),(1,x4,x0)] (by decide +kernel)
def p229 := prefixPool s27 [(0,x28,x1),(3,x30,x0)] (by decide +kernel)
def p230 := prefixPool s27 [(0,x4,x0)] (by decide +kernel)
def p231 := prefixPool s27 [(0,x4,x0),(0,x5,x1)] (by decide +kernel)
def p232 := prefixPool s27 [(0,x4,x0),(1,x5,x1)] (by decide +kernel)
def p233 := prefixPool s27 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p234 := prefixPool s27 [(0,x4,x0),(1,x4,x0),(0,x10,x1)] (by decide +kernel)
def p235 := prefixPool s27 [(0,x4,x0),(3,x5,x1)] (by decide +kernel)
def p236 := prefixPool s27 [(0,x4,x0),(3,x5,x1),(1,x4,x0)] (by decide +kernel)
def p237 := prefixPool s27 [(0,x4,x1)] (by decide +kernel)
def p238 := prefixPool s27 [(0,x4,x1),(0,x28,x1),(1,x30,x4)] (by decide +kernel)
def p239 := prefixPool s27 [(0,x4,x1),(1,x7,x0)] (by decide +kernel)
def p240 := prefixPool s27 [(0,x0,x1)] (by decide +kernel)
def p241 := prefixPool s27 [(0,x0,x1),(0,x28,x1),(1,x30,x0)] (by decide +kernel)
def p242 := prefixPool s27 [(0,x0,x1),(1,x9,x4)] (by decide +kernel)
def p243 := prefixPool s27 [(0,x0,x1),(3,x9,x4)] (by decide +kernel)
def p244 := prefixPool s27 [(1,x4,x0)] (by decide +kernel)
def p245 := prefixPool s27 [(1,x4,x0),(0,x10,x28)] (by decide +kernel)
def p246 := prefixPool s27 [(1,x4,x0),(0,x10,x28),(0,x4,x0)] (by decide +kernel)
def p247 := prefixPool s27 [(1,x4,x0),(0,x10,x1)] (by decide +kernel)
def p248 := prefixPool s27 [(1,x4,x0),(1,x10,x1)] (by decide +kernel)
def p249 := prefixPool s27 [(1,x4,x0),(3,x10,x1)] (by decide +kernel)
def p250 := prefixPool s27 [(1,x4,x1)] (by decide +kernel)
def p251 := prefixPool s27 [(1,x4,x1),(2,x12,x0)] (by decide +kernel)
def p252 := prefixPool s27 [(2,x28,x4)] (by decide +kernel)
def p253 := prefixPool s27 [(2,x28,x4),(3,x31,x0)] (by decide +kernel)
def p254 := prefixPool s27 [(2,x28,x0)] (by decide +kernel)
def p255 := prefixPool s27 [(2,x28,x0),(1,x32,x4)] (by decide +kernel)
def p256 := prefixPool s27 [(2,x4,x0)] (by decide +kernel)
def p257 := prefixPool s27 [(2,x4,x0),(0,x28,x0)] (by decide +kernel)
def p258 := prefixPool s27 [(2,x4,x0),(0,x4,x0)] (by decide +kernel)
def p259 := prefixPool s27 [(2,x4,x0),(1,x15,x1)] (by decide +kernel)
def p260 := prefixPool s27 [(2,x4,x0),(1,x4,x0)] (by decide +kernel)
def p261 := prefixPool s27 [(2,x4,x0),(3,x15,x1)] (by decide +kernel)
def p262 := prefixPool s27 [(2,x0,x1),(3,x33,x4)] (by decide +kernel)
def p263 := prefixPool s27 [(3,x4,x0)] (by decide +kernel)
def p264 := prefixPool s27 [(3,x4,x0),(0,x28,x4)] (by decide +kernel)
def p265 := prefixPool s27 [(3,x4,x0),(3,x18,x1)] (by decide +kernel)
def p266 := prefixPool s27 [(3,x4,x1)] (by decide +kernel)
def p267 := prefixPool s27 [(3,x4,x1),(0,x4,x1)] (by decide +kernel)
def p268 := prefixPool s27 [(3,x4,x1),(1,x34,x0)] (by decide +kernel)
def p269 := prefixPool s27 [(3,x0,x1)] (by decide +kernel)
def p270 := prefixPool s27 [(3,x0,x1),(1,x21,x4)] (by decide +kernel)
def p271 := prefixPool s27 [(3,x0,x1),(3,x21,x4)] (by decide +kernel)
def p272 := prefixPool s28 [] (by decide +kernel)
def p273 := prefixPool s29 [] (by decide +kernel)
def p274 := prefixPool s30 [] (by decide +kernel)
def p275 := prefixPool s30 [(0,x4,x0)] (by decide +kernel)
def p276 := prefixPool s30 [(0,x4,x0),(0,x5,x3)] (by decide +kernel)
def p277 := prefixPool s30 [(0,x4,x0),(1,x5,x28)] (by decide +kernel)
def p278 := prefixPool s30 [(0,x4,x0),(1,x5,x28),(1,x4,x0)] (by decide +kernel)
def p279 := prefixPool s30 [(0,x4,x0),(1,x5,x3)] (by decide +kernel)
def p280 := prefixPool s30 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p281 := prefixPool s30 [(0,x4,x0),(3,x5,x3)] (by decide +kernel)
def p282 := prefixPool s30 [(0,x4,x3)] (by decide +kernel)
def p283 := prefixPool s30 [(0,x4,x3),(1,x4,x3)] (by decide +kernel)
def p284 := prefixPool s30 [(0,x4,x3),(3,x6,x0)] (by decide +kernel)
def p285 := prefixPool s30 [(0,x0,x3)] (by decide +kernel)
def p286 := prefixPool s30 [(0,x0,x3),(1,x8,x4)] (by decide +kernel)
def p287 := prefixPool s30 [(0,x0,x3),(3,x8,x4)] (by decide +kernel)
def p288 := prefixPool s30 [(1,x4,x0)] (by decide +kernel)
def p289 := prefixPool s30 [(1,x4,x0),(0,x4,x0),(1,x5,x3)] (by decide +kernel)
def p290 := prefixPool s30 [(1,x4,x0),(0,x10,x3)] (by decide +kernel)
def p291 := prefixPool s30 [(1,x4,x0),(2,x10,x3)] (by decide +kernel)
def p292 := prefixPool s30 [(1,x4,x3)] (by decide +kernel)
def p293 := prefixPool s30 [(2,x4,x0)] (by decide +kernel)
def p294 := prefixPool s30 [(2,x4,x0),(0,x15,x3)] (by decide +kernel)
def p295 := prefixPool s30 [(2,x4,x0),(0,x4,x0)] (by decide +kernel)
def p296 := prefixPool s30 [(2,x4,x0),(1,x4,x3)] (by decide +kernel)
def p297 := prefixPool s30 [(2,x4,x3)] (by decide +kernel)
def p298 := prefixPool s30 [(2,x4,x3),(1,x4,x0)] (by decide +kernel)
def p299 := prefixPool s30 [(3,x4,x0)] (by decide +kernel)
def p300 := prefixPool s30 [(3,x4,x3)] (by decide +kernel)
def p301 := prefixPool s30 [(3,x4,x3),(3,x19,x0)] (by decide +kernel)
def p302 := prefixPool s30 [(3,x0,x3)] (by decide +kernel)
def p303 := prefixPool s30 [(3,x0,x3),(1,x20,x4)] (by decide +kernel)
def p304 := prefixPool s30 [(3,x0,x3),(3,x20,x4)] (by decide +kernel)
def p305 := prefixPool s31 [] (by decide +kernel)
def p306 := prefixPool s34 [] (by decide +kernel)
def p307 := prefixPool s34 [(0,x4,x0)] (by decide +kernel)
def p308 := prefixPool s34 [(0,x4,x0),(1,x5,x28)] (by decide +kernel)
def p309 := prefixPool s34 [(0,x4,x0),(1,x5,x28),(1,x4,x0)] (by decide +kernel)
def p310 := prefixPool s34 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p311 := prefixPool s34 [(1,x4,x0)] (by decide +kernel)
def p312 := prefixPool s34 [(2,x4,x0)] (by decide +kernel)
def p313 := prefixPool s34 [(2,x4,x0),(1,x4,x0)] (by decide +kernel)
def p314 := prefixPool s34 [(3,x4,x0)] (by decide +kernel)
def p315 := prefixPool s40 [] (by decide +kernel)
def p316 := prefixPool s43 [] (by decide +kernel)
def p317 := prefixPool s43 [(1,x2,x1)] (by decide +kernel)
def p318 := prefixPool s48 [] (by decide +kernel)
def p319 := prefixPool s53 [] (by decide +kernel)
def p320 := prefixPool s56 [] (by decide +kernel)
def p321 := prefixPool s56 [(1,x2,x1)] (by decide +kernel)
def p322 := prefixPool s61 [] (by decide +kernel)
def p323 := prefixPool s66 [] (by decide +kernel)
def p324 := prefixPool s71 [] (by decide +kernel)
def p325 := prefixPool s98 [] (by decide +kernel)
def p326 := prefixPool s100 [] (by decide +kernel)
def p327 := prefixPool s103 [] (by decide +kernel)
def p328 := prefixPool s103 [(1,x28,x2)] (by decide +kernel)
def p329 := prefixPool s113 [] (by decide +kernel)
def p330 := prefixPool s115 [] (by decide +kernel)
def p331 := prefixPool s118 [] (by decide +kernel)
def p332 := prefixPool s118 [(1,x28,x2)] (by decide +kernel)
def p333 := prefixPool s138 [] (by decide +kernel)
def p334 := prefixPool s140 [] (by decide +kernel)
def p335 := prefixPool s142 [] (by decide +kernel)
def p336 := prefixPool s144 [] (by decide +kernel)
def p337 := prefixPool s151 [] (by decide +kernel)
def p338 := prefixPool s151 [(0,x28,x4)] (by decide +kernel)
def p339 := prefixPool s151 [(0,x28,x2)] (by decide +kernel)
def p340 := prefixPool s151 [(0,x4,x0)] (by decide +kernel)
def p341 := prefixPool s151 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p342 := prefixPool s151 [(0,x4,x0),(1,x4,x0),(0,x10,x28)] (by decide +kernel)
def p343 := prefixPool s151 [(1,x4,x0)] (by decide +kernel)
def p344 := prefixPool s151 [(2,x28,x0)] (by decide +kernel)
def p345 := prefixPool s151 [(2,x4,x0)] (by decide +kernel)
def p346 := prefixPool s152 [] (by decide +kernel)
def p347 := prefixPool s155 [] (by decide +kernel)
def p348 := prefixPool s155 [(0,x4,x0)] (by decide +kernel)
def p349 := prefixPool s155 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p350 := prefixPool s155 [(1,x4,x0)] (by decide +kernel)
def p351 := prefixPool s155 [(2,x4,x0)] (by decide +kernel)
def p352 := prefixPool s160 [] (by decide +kernel)
def p353 := prefixPool s160 [(0,x28,x4)] (by decide +kernel)
def p354 := prefixPool s160 [(0,x28,x4),(1,x28,x4)] (by decide +kernel)
def p355 := prefixPool s160 [(0,x4,x2)] (by decide +kernel)
def p356 := prefixPool s160 [(0,x4,x1)] (by decide +kernel)
def p357 := prefixPool s160 [(1,x28,x4)] (by decide +kernel)
def p358 := prefixPool s160 [(1,x28,x4),(0,x35,x1)] (by decide +kernel)
def p359 := prefixPool s160 [(1,x28,x2)] (by decide +kernel)
def p360 := prefixPool s160 [(2,x28,x4)] (by decide +kernel)
def p361 := prefixPool s160 [(2,x4,x2)] (by decide +kernel)
def p362 := prefixPool s161 [] (by decide +kernel)
def p363 := prefixPool s161 [(0,x28,x4)] (by decide +kernel)
def p364 := prefixPool s161 [(0,x4,x2)] (by decide +kernel)
def p365 := prefixPool s161 [(1,x28,x4)] (by decide +kernel)
def p366 := prefixPool s161 [(1,x28,x2)] (by decide +kernel)
def p367 := prefixPool s161 [(2,x28,x4)] (by decide +kernel)
def p368 := prefixPool s161 [(2,x4,x2)] (by decide +kernel)
def p369 := prefixPool s170 [] (by decide +kernel)
def p370 := prefixPool s170 [(0,x28,x4)] (by decide +kernel)
def p371 := prefixPool s170 [(0,x28,x1)] (by decide +kernel)
def p372 := prefixPool s170 [(0,x4,x0)] (by decide +kernel)
def p373 := prefixPool s170 [(1,x4,x0)] (by decide +kernel)
def p374 := prefixPool s170 [(2,x4,x0)] (by decide +kernel)
def p375 := prefixPool s170 [(3,x0,x1)] (by decide +kernel)
def p376 := prefixPool s173 [] (by decide +kernel)
def p377 := prefixPool s173 [(0,x4,x0)] (by decide +kernel)
def p378 := prefixPool s173 [(1,x4,x0)] (by decide +kernel)
def p379 := prefixPool s173 [(2,x4,x0)] (by decide +kernel)
def p380 := prefixPool s173 [(3,x4,x0)] (by decide +kernel)
def p381 := prefixPool s173 [(3,x4,x0),(0,x4,x0)] (by decide +kernel)
def p382 := prefixPool s175 [] (by decide +kernel)
def p383 := prefixPool s180 [] (by decide +kernel)
def p384 := prefixPool s188 [] (by decide +kernel)
def p385 := prefixPool s188 [(0,x28,x1)] (by decide +kernel)
def p386 := prefixPool s188 [(0,x4,x0)] (by decide +kernel)
def p387 := prefixPool s188 [(1,x4,x0)] (by decide +kernel)
def p388 := prefixPool s188 [(2,x4,x0)] (by decide +kernel)
def p389 := prefixPool s188 [(3,x4,x1)] (by decide +kernel)
def p390 := prefixPool s191 [] (by decide +kernel)
def p391 := prefixPool s191 [(2,x4,x0)] (by decide +kernel)
def p392 := prefixPool s198 [] (by decide +kernel)
def p393 := prefixPool s198 [(0,x4,x0)] (by decide +kernel)
def p394 := prefixPool s198 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p395 := prefixPool s198 [(1,x4,x0)] (by decide +kernel)
def p396 := prefixPool s198 [(2,x4,x0)] (by decide +kernel)
def p397 := prefixPool s209 [] (by decide +kernel)
def p398 := prefixPool s209 [(0,x28,x4)] (by decide +kernel)
def p399 := prefixPool s209 [(0,x28,x2)] (by decide +kernel)
def p400 := prefixPool s209 [(0,x28,x2),(0,x4,x2)] (by decide +kernel)
def p401 := prefixPool s209 [(0,x28,x2),(0,x0,x2)] (by decide +kernel)
def p402 := prefixPool s209 [(0,x4,x0)] (by decide +kernel)
def p403 := prefixPool s209 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p404 := prefixPool s209 [(0,x4,x0),(1,x4,x0),(0,x10,x2)] (by decide +kernel)
def p405 := prefixPool s209 [(0,x4,x2)] (by decide +kernel)
def p406 := prefixPool s209 [(0,x0,x2)] (by decide +kernel)
def p407 := prefixPool s209 [(1,x4,x0)] (by decide +kernel)
def p408 := prefixPool s209 [(2,x28,x0)] (by decide +kernel)
def p409 := prefixPool s209 [(2,x4,x0)] (by decide +kernel)
def p410 := prefixPool s209 [(2,x4,x2)] (by decide +kernel)
def p411 := prefixPool s209 [(3,x4,x0)] (by decide +kernel)
def p412 := prefixPool s209 [(3,x0,x2)] (by decide +kernel)
def p413 := prefixPool s210 [] (by decide +kernel)
def p414 := prefixPool s211 [] (by decide +kernel)
def p415 := prefixPool s211 [(0,x4,x0)] (by decide +kernel)
def p416 := prefixPool s211 [(0,x4,x0),(1,x4,x0)] (by decide +kernel)
def p417 := prefixPool s211 [(1,x4,x0)] (by decide +kernel)
def p418 := prefixPool s211 [(2,x4,x0)] (by decide +kernel)
def q0 := usePool p0
def q1 := joinPools p0 p4
def q2 := joinPools p0 p19
def q3 := joinPools p0 p92
def q4 := usePool p1
def q5 := joinPools p1 p5
def q6 := joinPools p2 p317
def q7 := usePool p3
def q8 := usePool p4
def q9 := joinPools p4 p0
def q10 := usePool p6
def q11 := usePool p7
def q12 := usePool p8
def q13 := joinPools p9 p321
def q14 := usePool p10
def q15 := usePool p11
def q16 := usePool p12
def q17 := usePool p13
def q18 := usePool p14
def q19 := usePool p15
def q20 := usePool p16
def q21 := usePool p17
def q22 := usePool p18
def q23 := usePool p19
def q24 := usePool p20
def q25 := usePool p21
def q26 := usePool p22
def q27 := usePool p23
def q28 := usePool p24
def q29 := usePool p25
def q30 := usePool p26
def q31 := usePool p27
def q32 := usePool p28
def q33 := usePool p29
def q34 := usePool p30
def q35 := usePool p31
def q36 := usePool p32
def q37 := usePool p33
def q38 := usePool p34
def q39 := usePool p35
def q40 := usePool p36
def q41 := usePool p37
def q42 := usePool p38
def q43 := usePool p39
def q44 := usePool p40
def q45 := usePool p41
def q46 := usePool p42
def q47 := usePool p43
def q48 := usePool p44
def q49 := usePool p45
def q50 := usePool p46
def q51 := usePool p47
def q52 := usePool p48
def q53 := usePool p49
def q54 := usePool p50
def q55 := usePool p51
def q56 := usePool p52
def q57 := usePool p53
def q58 := usePool p54
def q59 := usePool p55
def q60 := usePool p56
def q61 := usePool p57
def q62 := usePool p58
def q63 := usePool p59
def q64 := usePool p60
def q65 := usePool p61
def q66 := usePool p62
def q67 := usePool p63
def q68 := usePool p64
def q69 := usePool p65
def q70 := usePool p66
def q71 := usePool p67
def q72 := usePool p68
def q73 := usePool p69
def q74 := usePool p70
def q75 := usePool p71
def q76 := usePool p72
def q77 := usePool p73
def q78 := usePool p74
def q79 := usePool p75
def q80 := usePool p76
def q81 := usePool p77
def q82 := usePool p78
def q83 := usePool p79
def q84 := usePool p80
def q85 := usePool p81
def q86 := usePool p82
def q87 := usePool p83
def q88 := usePool p84
def q89 := usePool p85
def q90 := usePool p86
def q91 := usePool p87
def q92 := usePool p88
def q93 := usePool p89
def q94 := usePool p90
def q95 := usePool p91
def q96 := usePool p92
def q97 := usePool p95
def q98 := usePool p96
def q99 := usePool p97
def q100 := usePool p98
def q101 := usePool p99
def q102 := usePool p100
def q103 := usePool p101
def q104 := usePool p102
def q105 := usePool p104
def q106 := usePool p105
def q107 := usePool p106
def q108 := usePool p107
def q109 := usePool p108
def q110 := usePool p111
def q111 := usePool p112
def q112 := usePool p113
def q113 := usePool p114
def q114 := usePool p115
def q115 := usePool p116
def q116 := usePool p117
def q117 := usePool p118
def q118 := usePool p120
def q119 := usePool p121
def q120 := usePool p122
def q121 := usePool p123
def q122 := usePool p124
def q123 := usePool p125
def q124 := usePool p126
def q125 := usePool p127
def q126 := usePool p128
def q127 := usePool p129
def q128 := usePool p130
def q129 := usePool p131
def q130 := usePool p132
def q131 := usePool p133
def q132 := usePool p134
def q133 := usePool p135
def q134 := usePool p136
def q135 := joinPools p136 p88
def q136 := usePool p137
def q137 := joinPools p137 p89
def q138 := usePool p138
def q139 := joinPools p139 p91
def q140 := joinPools p139 p94
def q141 := usePool p140
def q142 := joinPools p140 p4
def q143 := joinPools p140 p92
def q144 := usePool p141
def q145 := usePool p142
def q146 := joinPools p142 p107
def q147 := joinPools p143 p93
def q148 := joinPools p143 p107
def q149 := usePool p144
def q150 := usePool p145
def q151 := joinPools p145 p91
def q152 := joinPools p146 p107
def q153 := usePool p147
def q154 := usePool p148
def q155 := usePool p149
def q156 := joinPools p149 p103
def q157 := usePool p150
def q158 := usePool p151
def q159 := usePool p152
def q160 := usePool p153
def q161 := usePool p154
def q162 := usePool p155
def q163 := usePool p156
def q164 := usePool p157
def q165 := joinPools p157 p115
def q166 := usePool p158
def q167 := usePool p159
def q168 := joinPools p159 p105
def q169 := usePool p160
def q170 := usePool p161
def q171 := joinPools p162 p109
def q172 := joinPools p162 p110
def q173 := usePool p163
def q174 := usePool p164
def q175 := usePool p165
def q176 := usePool p166
def q177 := joinPools p166 p116
def q178 := usePool p167
def q179 := usePool p168
def q180 := usePool p169
def q181 := usePool p170
def q182 := joinPools p171 p119
def q183 := usePool p172
def q184 := usePool p173
def q185 := usePool p174
def q186 := usePool p175
def q187 := usePool p176
def q188 := usePool p177
def q189 := usePool p178
def q190 := usePool p179
def q191 := usePool p180
def q192 := usePool p181
def q193 := usePool p182
def q194 := usePool p183
def q195 := usePool p184
def q196 := usePool p185
def q197 := usePool p186
def q198 := usePool p187
def q199 := joinPools p188 p103
def q200 := usePool p189
def q201 := usePool p190
def q202 := usePool p191
def q203 := usePool p192
def q204 := usePool p193
def q205 := usePool p194
def q206 := usePool p195
def q207 := usePool p196
def q208 := usePool p197
def q209 := joinPools p197 p196
def q210 := joinPools p197 p280
def q211 := usePool p198
def q212 := usePool p199
def q213 := usePool p200
def q214 := usePool p201
def q215 := usePool p202
def q216 := usePool p203
def q217 := usePool p204
def q218 := usePool p205
def q219 := usePool p206
def q220 := usePool p207
def q221 := usePool p208
def q222 := usePool p209
def q223 := usePool p210
def q224 := usePool p211
def q225 := usePool p212
def q226 := usePool p213
def q227 := usePool p214
def q228 := usePool p215
def q229 := joinPools p215 p15
def q230 := usePool p216
def q231 := usePool p217
def q232 := usePool p218
def q233 := usePool p219
def q234 := usePool p220
def q235 := usePool p221
def q236 := joinPools p222 p279
def q237 := joinPools p223 p289
def q238 := usePool p224
def q239 := usePool p225
def q240 := joinPools p225 p283
def q241 := usePool p226
def q242 := usePool p227
def q243 := joinPools p228 p291
def q244 := usePool p229
def q245 := usePool p230
def q246 := joinPools p230 p16
def q247 := usePool p231
def q248 := usePool p232
def q249 := usePool p233
def q250 := joinPools p233 p19
def q251 := usePool p234
def q252 := usePool p235
def q253 := joinPools p235 p279
def q254 := joinPools p236 p289
def q255 := usePool p237
def q256 := usePool p238
def q257 := usePool p239
def q258 := usePool p240
def q259 := usePool p241
def q260 := usePool p242
def q261 := usePool p243
def q262 := usePool p244
def q263 := joinPools p244 p40
def q264 := usePool p245
def q265 := usePool p246
def q266 := usePool p247
def q267 := joinPools p247 p291
def q268 := usePool p248
def q269 := usePool p249
def q270 := usePool p250
def q271 := usePool p251
def q272 := usePool p252
def q273 := usePool p253
def q274 := usePool p254
def q275 := usePool p255
def q276 := usePool p256
def q277 := joinPools p256 p58
def q278 := usePool p257
def q279 := usePool p258
def q280 := usePool p259
def q281 := usePool p260
def q282 := usePool p261
def q283 := usePool p262
def q284 := usePool p263
def q285 := usePool p264
def q286 := usePool p265
def q287 := usePool p266
def q288 := usePool p267
def q289 := usePool p268
def q290 := usePool p269
def q291 := usePool p270
def q292 := usePool p271
def q293 := usePool p272
def q294 := usePool p273
def q295 := usePool p274
def q296 := usePool p275
def q297 := usePool p276
def q298 := usePool p277
def q299 := usePool p278
def q300 := usePool p279
def q301 := usePool p280
def q302 := usePool p281
def q303 := usePool p282
def q304 := usePool p283
def q305 := usePool p284
def q306 := usePool p285
def q307 := usePool p286
def q308 := usePool p287
def q309 := usePool p288
def q310 := usePool p289
def q311 := usePool p290
def q312 := usePool p291
def q313 := usePool p292
def q314 := usePool p293
def q315 := usePool p294
def q316 := usePool p295
def q317 := usePool p296
def q318 := usePool p297
def q319 := usePool p298
def q320 := usePool p299
def q321 := usePool p300
def q322 := usePool p301
def q323 := usePool p302
def q324 := usePool p303
def q325 := usePool p304
def q326 := joinPools p305 p328
def q327 := joinPools p305 p332
def q328 := usePool p306
def q329 := usePool p307
def q330 := usePool p308
def q331 := usePool p309
def q332 := usePool p310
def q333 := usePool p311
def q334 := usePool p312
def q335 := usePool p313
def q336 := usePool p314
def q337 := usePool p315
def q338 := usePool p316
def q339 := usePool p318
def q340 := usePool p319
def q341 := usePool p320
def q342 := usePool p322
def q343 := usePool p323
def q344 := usePool p324
def q345 := usePool p325
def q346 := usePool p326
def q347 := usePool p327
def q348 := usePool p329
def q349 := usePool p330
def q350 := usePool p331
def q351 := usePool p333
def q352 := usePool p334
def q353 := usePool p335
def q354 := usePool p336
def q355 := usePool p337
def q356 := usePool p338
def q357 := usePool p339
def q358 := joinPools p339 p307
def q359 := joinPools p339 p312
def q360 := usePool p340
def q361 := joinPools p340 p336
def q362 := joinPools p340 p346
def q363 := joinPools p340 p362
def q364 := usePool p341
def q365 := usePool p342
def q366 := usePool p343
def q367 := usePool p344
def q368 := usePool p345
def q369 := usePool p346
def q370 := usePool p347
def q371 := usePool p348
def q372 := usePool p349
def q373 := usePool p350
def q374 := usePool p351
def q375 := usePool p352
def q376 := usePool p353
def q377 := usePool p354
def q378 := usePool p355
def q379 := usePool p356
def q380 := usePool p357
def q381 := usePool p358
def q382 := usePool p359
def q383 := usePool p360
def q384 := usePool p361
def q385 := usePool p362
def q386 := usePool p363
def q387 := usePool p364
def q388 := usePool p365
def q389 := usePool p366
def q390 := usePool p367
def q391 := usePool p368
def q392 := usePool p369
def q393 := usePool p370
def q394 := usePool p371
def q395 := usePool p372
def q396 := usePool p373
def q397 := usePool p374
def q398 := usePool p375
def q399 := usePool p376
def q400 := usePool p377
def q401 := usePool p378
def q402 := usePool p379
def q403 := usePool p380
def q404 := usePool p381
def q405 := usePool p382
def q406 := usePool p383
def q407 := usePool p384
def q408 := usePool p385
def q409 := usePool p386
def q410 := usePool p387
def q411 := usePool p388
def q412 := usePool p389
def q413 := usePool p390
def q414 := usePool p391
def q415 := usePool p392
def q416 := usePool p393
def q417 := usePool p394
def q418 := usePool p395
def q419 := usePool p396
def q420 := usePool p397
def q421 := usePool p398
def q422 := usePool p399
def q423 := joinPools p399 p307
def q424 := joinPools p400 p308
def q425 := joinPools p401 p308
def q426 := usePool p402
def q427 := joinPools p402 p352
def q428 := usePool p403
def q429 := usePool p404
def q430 := usePool p405
def q431 := usePool p406
def q432 := usePool p407
def q433 := usePool p408
def q434 := usePool p409
def q435 := usePool p410
def q436 := joinPools p411 p335
def q437 := joinPools p411 p413
def q438 := usePool p412
def q439 := joinPools p412 p352
def q440 := usePool p414
def q441 := usePool p415
def q442 := usePool p416
def q443 := usePool p417
def q444 := usePool p418
def cc (k : Nat) (w : List (Observed (asRow Pos) (asRow Neg))) (ps : List (ChosenPool R T))
    (ns : List (Closed T (k-1))) (h : stateCheck k w (fun _ => (ps,ns)) = true) : Closed T k :=
  closeState (raw := R) correctPairs k w (fun _ => (ps,ns)) h
def n0 := cc 7 [w0,w6,w9,w3,w4,w5] [q23,q141,q375] [] (by decide +kernel)
def n1 := cc 8 [w0,w6,w1,w8,w3,w4,w5] [q0,q8,q136,q207,q212,q352] [n0] (by decide +kernel)
def n2 := cc 8 [w0,w6,w1,w11,w2,w3,w4,w5] [q8,q136,q176,q208,q214] [] (by decide +kernel)
def n3 := cc 8 [w12,w0,w1,w11,w2,w3,w4,w5] [q11,q136,q176,q208,q375] [] (by decide +kernel)
def n4 := cc 8 [w12,w0,w1,w8,w3,w4,w5] [q8,q176,q352,q375] [] (by decide +kernel)
def n5 := cc 8 [w0,w13,w1,w2,w8,w3,w4,w5] [q44,q72,q106,q136,q352] [] (by decide +kernel)
def n6 := cc 8 [w0,w1,w2,w9,w3,w4,w5] [q44,q106,q167,q351,q352] [n0] (by decide +kernel)
def n7 := cc 8 [w12,w0,w1,w2,w3,w4,w5] [q20,q62,q115,q176,q351,q352] [] (by decide +kernel)
def n8 := cc 8 [w0,w14,w1,w2,w8,w3,w4,w5] [q8,q106,q154,q207,q375] [] (by decide +kernel)
def n9 := cc 8 [w15,w0,w1,w11,w2,w3,w4,w5] [q11,q84,q203,q221,q228] [] (by decide +kernel)
def v0 : Closed T 8 := rotateClosed n4 auto1 auto1ok
def v1 : Closed T 8 := rotateClosed n1 auto1 auto1ok
def v2 : Closed T 8 := rotateClosed n5 auto1 auto1ok
def v3 : Closed T 8 := rotateClosed n8 auto1 auto1ok
def n10 := cc 9 [w0,w1,w11,w2,w3,w4,w5] [q19,q44,q106,q134,q208,q214,q392,q420] [n3,n7,v0,n9,n2,v1,v2,v3,n6] (by decide +kernel)
def n11 := cc 8 [w17,w10,w0,w1,w2,w3,w4,w5] [q8,q17,q44,q160,q234] [] (by decide +kernel)
def n12 := cc 8 [w18,w17,w0,w1,w2,w3,w4,w5] [q8,q17,q160,q274] [] (by decide +kernel)
def n13 := cc 8 [w17,w19,w0,w1,w2,w3,w4,w5] [q8,q17,q44,q160,q208,q219,q235] [] (by decide +kernel)
def n14 := cc 8 [w17,w0,w6,w2,w3,w4,w5] [q8,q17,q245] [n0] (by decide +kernel)
def n15 := cc 8 [w12,w21,w0,w1,w3,w4,w5] [q8,q215,q262,q276] [] (by decide +kernel)
def n16 := cc 8 [w17,w0,w1,w22,w2,w3,w4,w5] [q17,q208,q258,q314] [] (by decide +kernel)
def n17 := cc 8 [w17,w23,w0,w1,w2,w3,w4,w5] [q17,q160,q208,q215,q219,q290] [] (by decide +kernel)
def v4 : Closed T 8 := rotateClosed n15 auto1 auto1ok
def n18 := cc 9 [w17,w0,w1,w2,w3,w4,w5] [q8,q19,q134,q208,q228,q314,q355] [n12,v4,n7,n17,n11,n13,n14,n16,n6] (by decide +kernel)
def n19 := cc 8 [w0,w1,w25,w2,w3,w4,w5] [q20,q89,q193,q270,q320,q351] [] (by decide +kernel)
def n20 := cc 8 [w27,w0,w1,w2,w3,w4,w5] [q8,q72,q87,q93,q187,q231,q420] [] (by decide +kernel)
def n21 := cc 8 [w24,w0,w1,w2,w9,w3,w4,w5] [q102,q159,q208,q224,q262,q366] [] (by decide +kernel)
def n22 := cc 8 [w12,w24,w0,w1,w2,w3,w4,w5] [q8,q17,q159,q176,q208,q276,q314,q368] [] (by decide +kernel)
def v5 : Closed T 8 := rotateClosed n20 auto2 auto2ok
def n23 := cc 9 [w24,w0,w1,w2,w3,w4,w5] [q88,q159,q224,q228,q295,q355] [n22,n21,v5,n19] (by decide +kernel)
def n24 := cc 8 [w29,w0,w1,w4,w5] [] [] (by decide +kernel)
def v6 : Closed T 8 := rotateClosed n24 auto3 auto3ok
def n25 := cc 9 [w7,w30,w2,w3,w4,w5] [q19,q92,q134] [v6] (by decide +kernel)
def n26 := cc 7 [w29,w0,w1,w9,w4,w5] [q44,q72,q207,q262,q309,q352] [] (by decide +kernel)
def n27 := cc 7 [w12,w32,w0,w2,w4,w5] [q44,q62,q207,q276,q314] [] (by decide +kernel)
def v7 : Closed T 7 := rotateClosed n27 auto1 auto1ok
def n28 := cc 8 [w29,w0,w1,w2,w4,w5] [q19,q218,q228,q295,q352,q406] [v7,n26] (by decide +kernel)
def n29 := cc 7 [w29,w0,w6,w1,w4,w5] [] [] (by decide +kernel)
def v8 : Closed T 7 := rotateClosed n29 auto3 auto3ok
def n30 := cc 8 [w7,w6,w30,w2,w3,w4,w5] [q8,q20,q72,q93,q136] [v8] (by decide +kernel)
def v9 : Closed T 7 := rotateClosed n26 auto3 auto3ok
def n31 := cc 8 [w7,w30,w2,w9,w3,w4,w5] [q44,q62,q106,q167,q351] [v9] (by decide +kernel)
def v10 : Closed T 7 := rotateClosed n27 auto2 auto2ok
def n32 := cc 8 [w12,w7,w30,w2,w3,w4,w5] [q8,q44,q62,q115,q176] [v10] (by decide +kernel)
def n33 := cc 8 [w12,w10,w1,w33,w3,w4,w5] [] [] (by decide +kernel)
def n34 := cc 8 [w7,w1,w34,w2,w3,w4] [q8,q19,q92,q134,q217,q356] [] (by decide +kernel)
def v11 : Closed T 8 := rotateClosed n33 auto1 auto1ok
def v12 : Closed T 8 := rotateClosed n28 auto3 auto3ok
def n35 := cc 9 [w7,w1,w30,w2,w3,w4,w5] [q8,q19,q92,q134,q351] [n32,v11,v12,n30,n34,n31] (by decide +kernel)
def n36 := cc 8 [w7,w0,w6,w9,w3,w4,w5] [q0,q141,q207,q212] [] (by decide +kernel)
def v13 : Closed T 8 := rotateClosed n14 auto3 auto3ok
def v14 : Closed T 8 := rotateClosed n2 auto1 auto1ok
def n37 := cc 9 [w7,w0,w6,w1,w2,w3,w4,w5] [q0,q8,q11,q17,q19,q136,q207,q212] [v13,n36,n30,v14,n1] (by decide +kernel)
def n38 := cc 8 [w35,w0,w1,w2,w3,w4,w5] [q17,q62,q262,q314] [] (by decide +kernel)
def n39 := cc 8 [w7,w0,w1,w2,w36,w3,w4,w5] [q11,q47,q106,q170,q393,q420] [] (by decide +kernel)
def v15 : Closed T 8 := rotateClosed n38 auto3 auto3ok
def v16 : Closed T 8 := rotateClosed n21 auto3 auto3ok
def n40 := cc 9 [w7,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q44,q106,q167,q208,q230] [v15,v16,n36,n39,n31] (by decide +kernel)
def v17 : Closed T 8 := rotateClosed n15 auto2 auto2ok
def n41 := cc 9 [w12,w7,w0,w1,w2,w3,w4,w5] [q8,q11,q92,q176,q207,q212] [v17,n32,n4] (by decide +kernel)
def n42 := cc 8 [w0,w37,w1,w2,w3,w4,w5] [q11,q44,q106,q176] [] (by decide +kernel)
def n43 := cc 8 [w7,w0,w1,w39,w2,w3,w4,w5] [q75,q123,q195,q285,q375,q421] [] (by decide +kernel)
def n44 := cc 8 [w12,w10,w0,w1,w16,w3,w4,w5] [q0,q11,q20,q62,q180,q208,q278] [] (by decide +kernel)
def n45 := cc 8 [w12,w10,w0,w1,w40,w3,w4,w5] [q0,q11,q115,q181,q218,q375] [] (by decide +kernel)
def v18 : Closed T 8 := rotateClosed n22 auto2 auto2ok
def v19 : Closed T 8 := rotateClosed n43 auto1 auto1ok
def n46 := cc 9 [w12,w10,w0,w1,w2,w3,w4,w5] [q0,q8,q11,q62,q115,q136,q176,q219,q234] [v18,n44,n45,n3,v19,n42] (by decide +kernel)
def v20 : Closed T 8 := rotateClosed n44 auto1 auto1ok
def v21 : Closed T 8 := rotateClosed n11 auto1 auto1ok
def v22 : Closed T 8 := rotateClosed n11 auto3 auto3ok
def n47 := cc 9 [w7,w0,w20,w1,w2,w3,w4,w5] [q8,q11,q19,q153,q219,q230] [v20,v21,v22] (by decide +kernel)
def n48 := cc 9 [w18,w0,w1,w16,w2,w3,w4,w5] [q0,q17,q19,q159,q219,q274] [n12] (by decide +kernel)
def n49 := cc 8 [w41,w0,w1,w16,w2,w3,w4,w5] [q17,q44,q207,q261,q314] [] (by decide +kernel)
def v23 : Closed T 8 := rotateClosed n45 auto1 auto1ok
def v24 : Closed T 8 := rotateClosed n49 auto3 auto3ok
def v25 : Closed T 8 := rotateClosed n16 auto3 auto3ok
def n50 := cc 9 [w7,w0,w14,w1,w2,w3,w4,w5] [q11,q92,q154,q207,q420] [v23,v24,v25,n8] (by decide +kernel)
def v26 : Closed T 8 := rotateClosed n17 auto2 auto2ok
def n51 := cc 9 [w15,w10,w0,w1,w2,w3,w4,w5] [q11,q84,q92,q203,q221,q234] [v26,n9] (by decide +kernel)
def n52 := cc 8 [w0,w1,w42,w2,w3,w4,w5] [q8,q44,q153,q234,q351] [] (by decide +kernel)
def v27 : Closed T 8 := rotateClosed n52 auto1 auto1ok
def n53 := cc 9 [w7,w0,w1,w16,w2,w3,w4,w5] [q0,q8,q11,q17,q19,q159,q219,q230] [v27] (by decide +kernel)
def n54 := cc 8 [w44,w0,w1,w2,w3,w4,w5] [q11,q19,q201,q230] [] (by decide +kernel)
def v28 : Closed T 8 := rotateClosed n54 auto2 auto2ok
def n55 := cc 9 [w18,w0,w20,w1,w2,w3,w4,w5] [q0,q8,q17,q19,q153,q208,q274,q352] [v28] (by decide +kernel)
def n56 := cc 8 [w0,w1,w45,w2,w3,w4,w5] [q115,q154,q345] [] (by decide +kernel)
def n57 := cc 8 [w7,w0,w1,w40,w2,w46,w3,w4,w5] [q106,q115,q123,q163,q421] [] (by decide +kernel)
def n58 := cc 8 [w7,w0,w1,w40,w2,w47,w3,w5] [q10,q11,q18,q33,q162,q230,q348,q421] [] (by decide +kernel)
def v29 : Closed T 8 := rotateClosed n56 auto1 auto1ok
def n59 := cc 9 [w7,w0,w1,w40,w2,w3,w4,w5] [q0,q11,q17,q33,q92,q161,q212,q223,q230,q420] [n57,n58,v29] (by decide +kernel)
def n60 := cc 8 [w48,w0,w1,w2,w3,w4,w5] [q11,q85,q123,q203,q233] [] (by decide +kernel)
def n61 := cc 9 [w15,w7,w0,w1,w2,w3,w4,w5] [q0,q8,q11,q84,q92,q203,q230,q420] [n60] (by decide +kernel)
def n62 := cc 5 [w52,w0,w1,w3,w4,w5] [] [] (by decide +kernel)
def v30 : Closed T 5 := rotateClosed n62 auto3 auto3ok
def n63 := cc 6 [w0,w54,w2,w55,w3,w4,w5] [] [v30] (by decide +kernel)
def n64 := cc 7 [w0,w54,w1,w2,w53,w3,w4,w5] [q8,q58,q73,q82,q159,q235,q343] [n63] (by decide +kernel)
def v31 : Closed T 6 := rotateClosed n63 auto1 auto1ok
def n65 := cc 7 [w0,w1,w56,w2,w57,w3,w4,w5] [q54,q74,q194,q235,q352,q408] [v31] (by decide +kernel)
def v32 : Closed T 5 := rotateClosed n62 auto1 auto1ok
def n66 := cc 6 [w59,w60,w0,w2,w3,w4,w5] [] [v32] (by decide +kernel)
def v33 : Closed T 6 := rotateClosed n66 auto3 auto3ok
def n67 := cc 7 [w61,w0,w1,w56,w2,w3,w4,w5] [q55,q352] [v33] (by decide +kernel)
def n68 := cc 7 [w59,w0,w1,w2,w3,w58,w4,w5] [q8,q49] [n66] (by decide +kernel)
def v34 : Closed T 7 := rotateClosed n68 auto3 auto3ok
def v35 : Closed T 7 := rotateClosed n64 auto1 auto1ok
def n69 := cc 8 [w0,w1,w56,w2,w3,w4,w5] [q8,q17,q54,q153,q235,q351,q352] [v34,n67,v35,n65] (by decide +kernel)
def n70 := cc 8 [w62,w10,w0,w1,w2,w3,w4,w5] [q8,q17,q166,q208,q219,q234] [] (by decide +kernel)
def v36 : Closed T 8 := rotateClosed n70 auto1 auto1ok
def v37 : Closed T 8 := rotateClosed n13 auto3 auto3ok
def v38 : Closed T 8 := rotateClosed n69 auto2 auto2ok
def n71 := cc 9 [w7,w0,w1,w2,w47,w3,w4,w5] [q0,q11,q19,q164,q207,q208,q219,q230,q420] [v36,v37,n58,v38] (by decide +kernel)
def v39 : Closed T 9 := rotateClosed n55 auto2 auto2ok
def v40 : Closed T 9 := rotateClosed n48 auto3 auto3ok
def v41 : Closed T 9 := rotateClosed n46 auto1 auto1ok
def v42 : Closed T 9 := rotateClosed n18 auto3 auto3ok
def v43 : Closed T 9 := rotateClosed n51 auto1 auto1ok
def v44 : Closed T 9 := rotateClosed n23 auto3 auto3ok
def v45 : Closed T 9 := rotateClosed n10 auto1 auto1ok
def n72 := cc 10 [w7,w0,w1,w2,w3,w4,w5] [q19,q92,q134,q228] [v39,v40,n41,v41,v42,n61,v43,v44,n37,n47,n50,n53,n59,n40,n71,n35,n25,v45] (by decide +kernel)
def n73 := cc 8 [w63,w0,w1,w2,w3,w4,w5] [q20,q93,q176,q351] [] (by decide +kernel)
def n74 := cc 7 [w64,w0,w30,w3,w4,w5] [q1,q351,q380,q388] [] (by decide +kernel)
def n75 := cc 7 [w0,w6,w34,w9,w3,w4] [q8,q23,q96,q351] [] (by decide +kernel)
def n76 := cc 7 [w65,w0,w6,w9,w3,w4] [q23,q96,q385] [] (by decide +kernel)
def n77 := cc 8 [w0,w6,w30,w9,w3,w4,w5] [q8,q23,q96,q217] [n76,n74,n75] (by decide +kernel)
def n78 := cc 8 [w0,w6,w1,w34,w2,w3,w4] [q8,q17,q20,q93,q134,q355] [n75] (by decide +kernel)
def n79 := cc 8 [w0,w6,w1,w34,w2,w3,w4,w5] [q8,q20,q93,q217,q360] [] (by decide +kernel)
def n80 := cc 8 [w65,w0,w6,w1,w2,w3,w4] [q17,q20,q62,q93,q136,q351] [n76] (by decide +kernel)
def n81 := cc 9 [w0,w6,w1,w30,w2,w3,w4,w5] [q8,q17,q20,q93,q136,q206] [n80,n73,n30,n78,n79,n77] (by decide +kernel)
def n82 := cc 8 [w0,w13,w2,w9,w3,w4,w5] [q44,q72,q106,q215,q352] [n0] (by decide +kernel)
def n83 := cc 8 [w0,w13,w1,w2,w9,w3,w4,w5] [q0,q8,q44,q72,q106,q141,q206,q366] [] (by decide +kernel)
def n84 := cc 8 [w66,w0,w1,w9,w3,w4,w5] [q44,q106,q351,q352] [n0] (by decide +kernel)
def n85 := cc 8 [w0,w1,w34,w2,w9,w3,w4] [q17,q44,q62,q106,q134,q217] [n75] (by decide +kernel)
def n86 := cc 8 [w65,w0,w1,w2,w9,w3,w4] [q17,q44,q62,q106,q167,q351] [n76] (by decide +kernel)
def v46 : Closed T 8 := rotateClosed n83 auto1 auto1ok
def v47 : Closed T 8 := rotateClosed n82 auto1 auto1ok
def n87 := cc 9 [w0,w1,w30,w2,w9,w3,w4,w5] [q11,q17,q44,q62,q106,q134,q217] [n86,n84,n31,n77,v46,v47,n85] (by decide +kernel)
def n88 := cc 8 [w0,w67,w1,w2,w3,w4,w5] [q72,q123,q136,q352] [] (by decide +kernel)
def n89 := cc 8 [w12,w38,w0,w30,w3,w4,w5] [q68,q380,q385] [n74] (by decide +kernel)
def n90 := cc 8 [w12,w0,w1,w68,w2,w3,w4,w5] [q20,q44,q62,q375,q385] [] (by decide +kernel)
def n91 := cc 7 [w12,w0,w34,w69,w2,w3,w4] [q8,q12,q136] [] (by decide +kernel)
def n92 := cc 8 [w12,w0,w1,w34,w2,w3,w4] [q8,q12,q17,q44,q62,q115,q134,q355] [n91] (by decide +kernel)
def n93 := cc 8 [w12,w0,w1,w34,w2,w3,w4,w5] [q8,q44,q62,q115,q176,q352,q368,q388] [] (by decide +kernel)
def n94 := cc 8 [w65,w12,w0,w1,w2,w3,w4] [q20,q44,q62,q115,q385] [] (by decide +kernel)
def v48 : Closed T 8 := rotateClosed n88 auto1 auto1ok
def n95 := cc 9 [w12,w0,w1,w30,w2,w3,w4,w5] [q8,q11,q17,q44,q62,q115,q176,q206] [n94,n89,n32,n90,n92,n93,v48] (by decide +kernel)
def n96 := cc 8 [w12,w0,w13,w2,w3,w4,w5] [q44,q62,q375,q385] [] (by decide +kernel)
def n97 := cc 8 [w12,w70,w0,w2,w3,w4,w5] [q8,q62,q115,q352] [] (by decide +kernel)
def n98 := cc 8 [w12,w0,w1,w2,w71,w3,w4] [q8,q62,q115,q134,q226] [] (by decide +kernel)
def n99 := cc 8 [w65,w38,w0,w1,w2,w3,w4] [q20,q44,q72,q123,q385] [] (by decide +kernel)
def v49 : Closed T 8 := rotateClosed n99 auto1 auto1ok
def v50 : Closed T 8 := rotateClosed n89 auto1 auto1ok
def n100 := cc 9 [w12,w0,w1,w2,w33,w3,w4,w5] [q8,q62,q115,q134,q226] [v49,v50,n97,n96,n98] (by decide +kernel)
def n101 := cc 8 [w0,w13,w1,w22,w2,w3,w4,w5] [q17,q37,q103,q136,q226] [] (by decide +kernel)
def n102 := cc 8 [w66,w0,w72,w1,w2,w3,w4,w5] [q8,q17,q30,q99,q176,q352] [] (by decide +kernel)
def v51 : Closed T 8 := rotateClosed n102 auto2 auto2ok
def v52 : Closed T 8 := rotateClosed n101 auto3 auto3ok
def n103 := cc 9 [w0,w14,w1,w2,w3,w31,w4,w5] [q26,q207,q214,q228,q303,q420] [v51,v52] (by decide +kernel)
def n104 := cc 8 [w0,w1,w73,w2,w3,w28,w4,w5] [q85,q208,q245,q284,q324,q352,q407] [] (by decide +kernel)
def n105 := cc 8 [w15,w0,w74,w1,w2,w3,w4,w5] [q84,q245,q323,q352,q375,q409] [] (by decide +kernel)
def n106 := cc 8 [w66,w75,w0,w1,w2,w3,w4,w5] [q17,q80,q128,q176,q351,q402] [] (by decide +kernel)
def v53 : Closed T 8 := rotateClosed n106 auto3 auto3ok
def n107 := cc 9 [w15,w0,w1,w2,w3,w28,w4,w5] [q84,q207,q228,q323,q352,q407] [v53,n105,n104] (by decide +kernel)
def n108 := cc 8 [w0,w6,w1,w2,w3,w4,w5] [q20,q93,q136,q351,q352] [n0] (by decide +kernel)
def v54 : Closed T 8 := rotateClosed n90 auto1 auto1ok
def v55 : Closed T 8 := rotateClosed n7 auto1 auto1ok
def v56 : Closed T 8 := rotateClosed n105 auto2 auto2ok
def n109 := cc 9 [w0,w13,w1,w2,w3,w4,w5] [q19,q92,q134,q215,q355] [n96,v54,v55,v56,n108,n101,n5,n83,n82] (by decide +kernel)
def v57 : Closed T 8 := rotateClosed n97 auto1 auto1ok
def n110 := cc 9 [w66,w0,w1,w2,w3,w4,w5] [q17,q19,q92,q134,q176,q352,q355] [v57,n7,n106,n102,n84,n108] (by decide +kernel)
def n111 := cc 7 [w76,w0,w1,w34,w2,w3,w4] [q56,q112,q351,q368] [] (by decide +kernel)
def n112 := cc 8 [w0,w1,w34,w69,w2,w3,w4] [q17,q54,q111,q134,q351,q355] [n91,n111] (by decide +kernel)
def n113 := cc 8 [w0,w1,w34,w2,w77,w3,w4] [q57,q113,q134,q217,q355] [] (by decide +kernel)
def n114 := cc 8 [w79,w0,w1,w2,w3,w78,w5] [q69,q207,q223,q318,q397] [] (by decide +kernel)
def v58 : Closed T 8 := rotateClosed n114 auto3 auto3ok
def v59 : Closed T 8 := rotateClosed n98 auto1 auto1ok
def n115 := cc 9 [w0,w1,w34,w2,w3,w4] [q19,q92,q134,q355] [v58,n92,v59,n34,n78,n112,n85,n113] (by decide +kernel)
def n116 := cc 8 [w0,w1,w2,w80,w3,w4,w5] [q54,q111,q167,q176,q351,q355] [] (by decide +kernel)
def n117 := cc 8 [w79,w0,w1,w2,w3,w4,w5] [q69,q262,q318,q375,q420] [] (by decide +kernel)
def v60 : Closed T 8 := rotateClosed n117 auto3 auto3ok
def v61 : Closed T 8 := rotateClosed n116 auto1 auto1ok
def n118 := cc 9 [w0,w1,w34,w2,w3,w4,w5] [q19,q92,q134,q217,q355] [v60,n93,n79,v61] (by decide +kernel)
def n119 := cc 9 [w65,w0,w1,w2,w3,w4] [q19,q92,q134] [n94,n99,n80,n86] (by decide +kernel)
def n120 := cc 8 [w0,w1,w33,w81,w3,w4,w5] [q8,q31,q100,q167,q355] [] (by decide +kernel)
def n121 := cc 8 [w41,w0,w30,w2,w3,w4,w5] [q8,q40,q105,q176,q355,q385] [] (by decide +kernel)
def n122 := cc 8 [w82,w0,w1,w2,w3,w4,w5] [q17,q37,q103,q176] [] (by decide +kernel)
def v62 : Closed T 8 := rotateClosed n121 auto3 auto3ok
def v63 : Closed T 8 := rotateClosed n122 auto3 auto3ok
def v64 : Closed T 8 := rotateClosed n120 auto2 auto2ok
def n123 := cc 9 [w0,w14,w1,w2,w3,w28,w4,w5] [q26,q207,q218,q228,q303,q352,q420] [v62,v63,v64] (by decide +kernel)
def n124 := cc 8 [w0,w83,w1,w2,w3,w4,w5] [q0,q8,q80,q128,q136] [] (by decide +kernel)
def v65 : Closed T 8 := rotateClosed n124 auto3 auto3ok
def n125 := cc 9 [w15,w0,w1,w2,w3,w31,w4,w5] [q84,q207,q214,q218,q219,q221,q228,q323,q407,q420] [v65] (by decide +kernel)
def v66 : Closed T 9 := rotateClosed n100 auto1 auto1ok
def v67 : Closed T 9 := rotateClosed n125 auto2 auto2ok
def v68 : Closed T 9 := rotateClosed n107 auto3 auto3ok
def v69 : Closed T 9 := rotateClosed n109 auto1 auto1ok
def v70 : Closed T 9 := rotateClosed n103 auto2 auto2ok
def v71 : Closed T 9 := rotateClosed n123 auto3 auto3ok
def n126 := cc 10 [w0,w1,w30,w2,w3,w4,w5] [q19,q92,q134] [n119,n95,v66,n110,v67,v68,n35,n25,n81,v69,v70,v71,n115,n118,n87] (by decide +kernel)
def n127 := cc 8 [w0,w1,w85,w9,w3,w4,w5] [q167,q208,q352] [n0] (by decide +kernel)
def n128 := cc 8 [w12,w0,w86,w2,w3,w4,w5] [q17,q68,q176,q208,q352] [] (by decide +kernel)
def n129 := cc 8 [w12,w0,w1,w86,w2,w3,w4,w5] [q8,q17,q68,q136,q176,q214,q275,q276,q352] [] (by decide +kernel)
def v72 : Closed T 8 := rotateClosed n127 auto1 auto1ok
def n130 := cc 9 [w0,w1,w86,w2,w3,w4,w5] [q19,q72,q134,q208,q214,q228,q341,q420] [n129,v55,n128,n108,v72] (by decide +kernel)
def n131 := cc 8 [w19,w0,w87,w1,w2,w3,w4,w5] [q8,q11,q19,q202,q208,q235] [] (by decide +kernel)
def n132 := cc 8 [w0,w87,w2,w9,w3,w4,w5] [q11,q208,q262] [n0] (by decide +kernel)
def n133 := cc 8 [w12,w0,w87,w2,w3,w4,w5] [q8,q276,q352] [] (by decide +kernel)
def n134 := cc 9 [w0,w87,w1,w2,w3,w4,w5] [q8,q19,q134,q208,q228,q296,q340,q349,q355] [n133,v55,n131,n108,n132] (by decide +kernel)
def n135 := cc 8 [w0,w1,w2,w89,w3,w4,w5] [q38,q62,q175,q270,q309,q351] [] (by decide +kernel)
def n136 := cc 8 [w91,w0,w1,w2,w3,w4,w5] [q36,q44,q93,q115,q187,q375,q411] [] (by decide +kernel)
def v73 : Closed T 8 := rotateClosed n136 auto3 auto3ok
def v74 : Closed T 8 := rotateClosed n135 auto1 auto1ok
def n137 := cc 9 [w0,w1,w93,w2,w3,w4,w5] [q30,q196,q207,q217,q228,q295,q355] [v73,v74] (by decide +kernel)
def v75 : Closed T 8 := rotateClosed n24 auto1 auto1ok
def n138 := cc 9 [w94,w92,w0,w2,w4,w5] [q19,q228,q295] [v75] (by decide +kernel)
def v76 : Closed T 7 := rotateClosed n29 auto1 auto1ok
def n139 := cc 8 [w94,w92,w0,w6,w2,w4,w5] [q8,q72,q245,q296] [v76] (by decide +kernel)
def v77 : Closed T 7 := rotateClosed n26 auto1 auto1ok
def n140 := cc 8 [w94,w92,w0,w2,w9,w4,w5] [q44,q62,q262,q309,q351] [v77] (by decide +kernel)
def n141 := cc 8 [w94,w12,w92,w0,w2,w4,w5] [q8,q44,q276,q314] [n27] (by decide +kernel)
def n142 := cc 7 [w12,w29,w0,w1,w4,w5] [] [] (by decide +kernel)
def v78 : Closed T 7 := rotateClosed n142 auto1 auto1ok
def n143 := cc 8 [w94,w38,w92,w0,w2,w4,w5] [q20,q72,q284,q320,q351] [v78] (by decide +kernel)
def v79 : Closed T 8 := rotateClosed n28 auto1 auto1ok
def n144 := cc 9 [w94,w92,w0,w1,w2,w4,w5] [q8,q19,q228,q295,q351] [n141,n143,n139,n140,v79] (by decide +kernel)
def n145 := cc 8 [w18,w0,w6,w9,w3,w4,w5] [q17,q141,q219] [] (by decide +kernel)
def v80 : Closed T 8 := rotateClosed n139 auto3 auto3ok
def n146 := cc 9 [w18,w0,w6,w1,w2,w3,w4,w5] [q0,q136,q176,q340,q341] [v80,n145,n88] (by decide +kernel)
def v81 : Closed T 8 := rotateClosed n140 auto3 auto3ok
def v82 : Closed T 8 := rotateClosed n132 auto2 auto2ok
def n147 := cc 9 [w18,w0,w1,w2,w9,w3,w4,w5] [q0,q92,q167,q219,q223] [v81,n145,v82,v72] (by decide +kernel)
def v83 : Closed T 8 := rotateClosed n143 auto3 auto3ok
def v84 : Closed T 8 := rotateClosed n133 auto2 auto2ok
def n148 := cc 9 [w18,w12,w0,w1,w2,w3,w4,w5] [q0,q8,q19,q136,q176,q219,q223] [v83,v84,n129,n128] (by decide +kernel)
def v85 : Closed T 8 := rotateClosed n141 auto3 auto3ok
def v86 : Closed T 8 := rotateClosed n73 auto1 auto1ok
def n149 := cc 9 [w18,w38,w0,w1,w2,w3,w4,w5] [q0,q19,q192,q219,q341] [v85,v86] (by decide +kernel)
def n150 := cc 8 [w95,w0,w1,w2,w3,w4,w5] [q8,q201,q272] [] (by decide +kernel)
def v87 : Closed T 8 := rotateClosed n150 auto1 auto1ok
def n151 := cc 9 [w18,w92,w0,w1,w2,w3,w4,w5] [q0,q17,q19,q196,q274,q352] [v87] (by decide +kernel)
def n152 := cc 8 [w0,w1,w96,w2,w3,w4,w5] [q123,q154,q340] [] (by decide +kernel)
def n153 := cc 8 [w18,w0,w14,w1,w2,w47,w3,w5] [q0,q10,q26,q155,q208,q274,q340,q433] [] (by decide +kernel)
def n154 := cc 9 [w18,w0,w14,w1,w2,w3,w4,w5] [q0,q8,q17,q26,q92,q154,q214,q222,q223,q274,q420] [n153,n152] (by decide +kernel)
def n155 := cc 8 [w97,w0,w1,w2,w3,w4,w5] [q8,q87,q93,q203,q273] [] (by decide +kernel)
def v88 : Closed T 8 := rotateClosed n155 auto1 auto1ok
def n156 := cc 9 [w18,w98,w0,w1,w2,w3,w4,w5] [q0,q17,q77,q92,q198,q274,q352,q392] [v88] (by decide +kernel)
def n157 := cc 9 [w18,w43,w0,w1,w2,w3,w4,w5] [q19,q201,q274,q340,q352] [] (by decide +kernel)
def n158 := cc 9 [w18,w0,w1,w40,w2,w3,w4,w5] [q17,q33,q92,q161,q219,q223] [] (by decide +kernel)
def n159 := cc 9 [w18,w15,w0,w1,w2,w3,w4,w5] [q84,q92,q203,q274,q341,q352,q407] [] (by decide +kernel)
def n160 := cc 8 [w0,w99,w1,w2,w3,w4,w5] [q8,q11,q201,q235,q351] [] (by decide +kernel)
def n161 := cc 8 [w62,w18,w0,w1,w2,w3,w4,w5] [q8,q17,q120,q166,q219] [] (by decide +kernel)
def v89 : Closed T 8 := rotateClosed n131 auto2 auto2ok
def v90 : Closed T 8 := rotateClosed n160 auto2 auto2ok
def n162 := cc 9 [w18,w0,w1,w2,w47,w3,w4,w5] [q0,q19,q92,q164,q208,q219,q407] [n161,n153,v89,v90] (by decide +kernel)
def v91 : Closed T 9 := rotateClosed n144 auto3 auto3ok
def v92 : Closed T 9 := rotateClosed n138 auto3 auto3ok
def v93 : Closed T 9 := rotateClosed n134 auto2 auto2ok
def v94 : Closed T 9 := rotateClosed n137 auto3 auto3ok
def n163 := cc 10 [w18,w0,w1,w2,w3,w4,w5] [q19,q92,q134,q228] [v91,v92,n148,n157,n159,n149,n151,n156,n146,n55,n154,n48,n158,n147,n162,v93,v94,n130] (by decide +kernel)
def n164 := cc 8 [w0,w6,w1,w100,w3,w4,w5] [q8,q208,q296] [n0] (by decide +kernel)
def n165 := cc 8 [w12,w0,w1,w100,w3,w4,w5] [q20,q62,q314,q375] [] (by decide +kernel)
def v95 : Closed T 8 := rotateClosed n165 auto1 auto1ok
def v96 : Closed T 8 := rotateClosed n164 auto1 auto1ok
def n166 := cc 9 [w0,w1,w102,w2,w3,w4,w5] [q19,q207,q228,q295,q348,q351,q420] [n7,v95,v96,n6] (by decide +kernel)
def n167 := cc 8 [w104,w19,w1,w2,w3,w4,w5] [q8,q11,q19,q92,q176] [] (by decide +kernel)
def n168 := cc 8 [w104,w0,w6,w2,w3,w4,w5] [q8,q11,q20,q93] [n0] (by decide +kernel)
def n169 := cc 8 [w12,w0,w106,w1,w3,w4,w5] [q0,q8,q62,q115] [] (by decide +kernel)
def n170 := cc 8 [w12,w0,w106,w1,w2,w3,w4,w5] [q11,q17,q44,q62,q115,q185,q206,q368] [] (by decide +kernel)
def v97 : Closed T 8 := rotateClosed n170 auto1 auto1ok
def v98 : Closed T 8 := rotateClosed n169 auto1 auto1ok
def n171 := cc 9 [w104,w0,w1,w2,w3,w4,w5] [q19,q92,q134,q215,q342,q355] [v97,v98,n7,n167,n168,n6] (by decide +kernel)
def n172 := cc 8 [w0,w1,w108,w2,w3,w4,w5] [q54,q111,q136,q355,q385] [] (by decide +kernel)
def n173 := cc 8 [w110,w0,w1,w2,w3,w4,w5] [q8,q219,q245,q284,q318] [] (by decide +kernel)
def v99 : Closed T 8 := rotateClosed n173 auto2 auto2ok
def n174 := cc 9 [w0,w107,w1,w2,w3,w4,w5] [q11,q19,q92,q134,q224,q355] [v99,n172] (by decide +kernel)
def n175 := cc 8 [w94,w0,w6,w9,w3,w4,w5] [q8,q23,q208,q301] [] (by decide +kernel)
def v100 : Closed T 8 := rotateClosed n168 auto3 auto3ok
def n176 := cc 9 [w94,w0,w6,w1,w2,w3,w4,w5] [q20,q212,q218,q228,q296] [n139,n175,v100,n164] (by decide +kernel)
def v101 : Closed T 8 := rotateClosed n42 auto3 auto3ok
def n177 := cc 9 [w94,w0,w1,w2,w9,w3,w4,w5] [q8,q44,q208,q218,q219,q262,q293,q309] [n140,n175,v101] (by decide +kernel)
def v102 : Closed T 8 := rotateClosed n170 auto2 auto2ok
def v103 : Closed T 8 := rotateClosed n169 auto2 auto2ok
def n178 := cc 9 [w94,w12,w0,w1,w2,w3,w4,w5] [q44,q62,q212,q218,q228,q314,q352] [n141,v102,v103,n165] (by decide +kernel)
def v104 : Closed T 8 := rotateClosed n38 auto1 auto1ok
def n179 := cc 9 [w94,w38,w0,w1,w2,w3,w4,w5] [q72,q120,q208,q218,q293,q320] [n143,v104] (by decide +kernel)
def n180 := cc 7 [w94,w0,w14,w2,w111,w5] [q29,q228,q304,q351,q435] [] (by decide +kernel)
def n181 := cc 8 [w94,w0,w14,w1,w2,w47,w5] [q10,q208,q218,q303] [n180] (by decide +kernel)
def n182 := cc 9 [w94,w0,w14,w1,w2,w3,w4,w5] [q8,q228,q303,q345,q392] [n181] (by decide +kernel)
def n183 := cc 9 [w94,w98,w0,w1,w2,w3,w4,w5] [q77,q208,q212,q228,q321] [] (by decide +kernel)
def n184 := cc 8 [w0,w1,w112,w2,w3,w4,w5] [q26,q207,q262,q303] [] (by decide +kernel)
def n185 := cc 8 [w94,w0,w2,w46,w3,w4,w5] [q35,q208,q262,q307] [] (by decide +kernel)
def n186 := cc 7 [w94,w113,w0,w2,w47,w5] [q10,q18,q276,q308] [] (by decide +kernel)
def n187 := cc 8 [w94,w113,w0,w2,w3,w4,w5] [q8,q17,q36,q276,q308,q397] [n186] (by decide +kernel)
def n188 := cc 8 [w94,w0,w1,w40,w2,w47,w5] [q18,q33,q211,q212,q228,q306,q435] [n186] (by decide +kernel)
def v105 : Closed T 8 := rotateClosed n184 auto1 auto1ok
def n189 := cc 9 [w94,w0,w1,w40,w2,w3,w4,w5] [q8,q33,q208,q218,q228,q306,q420] [n187,n188,n185,v105] (by decide +kernel)
def n190 := cc 8 [w114,w0,w1,w2,w3,w4,w5] [q84,q208,q323,q407] [] (by decide +kernel)
def n191 := cc 9 [w94,w15,w0,w1,w2,w3,w4,w5] [q84,q208,q212,q218,q219,q221,q228,q323,q407] [n190] (by decide +kernel)
def n192 := cc 8 [w94,w0,w1,w2,w111,w4,w5] [q52,q212,q228,q313,q351] [n180] (by decide +kernel)
def v106 : Closed T 8 := rotateClosed n167 auto3 auto3ok
def n193 := cc 9 [w94,w0,w1,w2,w47,w4,w5] [q19,q208,q212,q228,q295] [n181,n188,n192,v106] (by decide +kernel)
def v107 : Closed T 9 := rotateClosed n171 auto3 auto3ok
def v108 : Closed T 9 := rotateClosed n174 auto3 auto3ok
def v109 : Closed T 9 := rotateClosed n166 auto1 auto1ok
def n194 := cc 10 [w94,w0,w1,w2,w3,w4,w5] [q19,q228,q295] [n178,n191,n179,n144,n138,n183,n176,n182,n189,n177,n193,v107,v108,v109] (by decide +kernel)
def n195 := cc 8 [w117,w1,w2,w4,w5] [q92,q134,q351] [] (by decide +kernel)
def n196 := cc 7 [w115,w6,w9,w116,w4,w5] [q2,q8,q23,q96,q141,q351] [] (by decide +kernel)
def n197 := cc 8 [w115,w6,w1,w2,w116,w4,w5] [q20,q93,q136,q351,q352] [n196] (by decide +kernel)
def n198 := cc 7 [w115,w1,w2,w118,w4,w5] [q2,q106,q169,q351,q352] [] (by decide +kernel)
def n199 := cc 8 [w115,w1,w2,w9,w116,w4,w5] [q44,q106,q167,q351,q352] [n196,n198] (by decide +kernel)
def n200 := cc 8 [w12,w115,w1,w2,w116,w4,w5] [q20,q62,q115,q176,q351,q352] [] (by decide +kernel)
def v110 : Closed T 8 := rotateClosed n200 auto1 auto1ok
def n201 := cc 9 [w115,w1,w2,w116,w4,w5] [q19,q92,q134] [n200,v110,n195,n197,n199] (by decide +kernel)
def n202 := cc 8 [w115,w0,w6,w9,w3,w4,w5] [q0,q141,q337] [n196] (by decide +kernel)
def n203 := cc 9 [w115,w0,w6,w1,w2,w3,w4,w5] [q0,q11,q20,q136,q245] [n202,n197] (by decide +kernel)
def n204 := cc 9 [w115,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q44,q167,q262] [n202,n199] (by decide +kernel)
def n205 := cc 9 [w12,w115,w0,w1,w2,w3,w4,w5] [q0,q11,q20,q62,q176,q276] [n200] (by decide +kernel)
def v111 : Closed T 9 := rotateClosed n205 auto1 auto1ok
def n206 := cc 10 [w115,w0,w1,w2,w3,w4,w5] [q19,q134,q228] [n205,v111,n203,n204,n201] (by decide +kernel)
def n207 := cc 8 [w0,w119,w1,w2,w3,w4,w5] [q8,q72,q93,q296,q355,q420] [] (by decide +kernel)
def n208 := cc 8 [w120,w0,w1,w2,w3,w4,w5] [q8,q72,q93,q296] [] (by decide +kernel)
def n209 := cc 7 [w64,w0,w9,w3,w116,w4,w5] [q0,q1,q207,q382,q389] [] (by decide +kernel)
def n210 := cc 7 [w0,w6,w118,w3,w4,w5] [q2,q8,q23,q96,q301] [] (by decide +kernel)
def n211 := cc 7 [w0,w6,w118,w9,w3,w4,w5] [q0,q1,q8,q23,q96,q301] [] (by decide +kernel)
def n212 := cc 7 [w121,w0,w6,w3,w4,w5] [q8,q23,q96,q301,q351] [] (by decide +kernel)
def n213 := cc 8 [w0,w6,w9,w3,w116,w4,w5] [q8,q23,q96,q301,q351] [n212,n209,n196,n211,n210] (by decide +kernel)
def n214 := cc 7 [w0,w6,w123,w3,w4,w5] [q23,q301,q375] [] (by decide +kernel)
def v112 : Closed T 7 := rotateClosed n214 auto1 auto1ok
def n215 := cc 8 [w0,w6,w124,w2,w3,w4,w5] [q8,q72,q93,q296,q352] [v112] (by decide +kernel)
def n216 := cc 8 [w125,w0,w6,w1,w3,w4,w5] [q8,q72,q93,q296,q352] [n212] (by decide +kernel)
def v113 : Closed T 8 := rotateClosed n216 auto1 auto1ok
def v114 : Closed T 8 := rotateClosed n215 auto1 auto1ok
def n217 := cc 9 [w0,w6,w1,w2,w3,w116,w4,w5] [q8,q17,q93,q134,q228,q296] [n216,v113,n208,n197,n207,n215,v114,n213] (by decide +kernel)
def n218 := cc 8 [w0,w124,w1,w2,w9,w3,w4,w5] [q8,q17,q106,q309] [] (by decide +kernel)
def n219 := cc 8 [w0,w1,w2,w118,w3,w4,w5] [q8,q17,q44,q106,q309] [n198,n210] (by decide +kernel)
def n220 := cc 8 [w0,w1,w2,w118,w9,w3,w4,w5] [q8,q17,q44,q106,q309,q351] [n211] (by decide +kernel)
def n221 := cc 8 [w121,w0,w1,w2,w3,w4,w5] [q44,q106,q309,q351,q352] [n212] (by decide +kernel)
def v115 : Closed T 8 := rotateClosed n218 auto1 auto1ok
def n222 := cc 9 [w0,w1,w2,w9,w3,w116,w4,w5] [q8,q17,q106,q309,q351,q352] [n221,n199,n213,n218,v115,n220,n219] (by decide +kernel)
def n223 := cc 8 [w126,w0,w1,w2,w3,w4,w5] [q20,q62,q115,q314,q352] [] (by decide +kernel)
def n224 := cc 8 [w0,w1,w127,w2,w3,w4,w5] [q8,q123,q320,q351] [] (by decide +kernel)
def n225 := cc 8 [w12,w0,w1,w122,w3,w4,w5] [q8,q44,q115,q314] [] (by decide +kernel)
def n226 := cc 8 [w12,w0,w1,w122,w2,w3,w4,w5] [q8,q17,q44,q115,q314] [] (by decide +kernel)
def n227 := cc 8 [w12,w125,w0,w1,w3,w4,w5] [q20,q62,q115,q314,q351,q352] [] (by decide +kernel)
def v116 : Closed T 8 := rotateClosed n224 auto1 auto1ok
def n228 := cc 9 [w12,w0,w1,w2,w3,w116,w4,w5] [q8,q17,q44,q115,q314,q352] [n223,n227,n200,n226,n225,v116] (by decide +kernel)
def n229 := cc 8 [w0,w1,w2,w123,w3,w4,w5] [q17,q44,q62,q106,q309,q351] [n214] (by decide +kernel)
def n230 := cc 8 [w0,w124,w1,w2,w128,w3,w4,w5] [q8,q17,q106,q309] [] (by decide +kernel)
def n231 := cc 8 [w129,w0,w1,w2,w3,w4,w5] [q8,q17,q44,q115,q314] [] (by decide +kernel)
def n232 := cc 8 [w129,w0,w1,w122,w2,w3,w4,w5] [q8,q17,q44,q115,q314] [] (by decide +kernel)
def v117 : Closed T 8 := rotateClosed n226 auto1 auto1ok
def v118 : Closed T 8 := rotateClosed n225 auto1 auto1ok
def v119 : Closed T 8 := rotateClosed n232 auto1 auto1ok
def v120 : Closed T 8 := rotateClosed n231 auto1 auto1ok
def v121 : Closed T 8 := rotateClosed n229 auto1 auto1ok
def n233 := cc 9 [w0,w124,w1,w2,w3,w4,w5] [q8,q92,q295] [n223,v117,v118,v119,v120,n207,n215,n230,n218,v121] (by decide +kernel)
def n234 := cc 8 [w0,w1,w130,w2,w3,w4,w5] [q20,q72,q123,q320,q351,q352] [] (by decide +kernel)
def n235 := cc 8 [w0,w131,w1,w2,w3,w4,w5] [q20,q93,q296,q352,q375] [] (by decide +kernel)
def n236 := cc 9 [w125,w0,w1,w2,w3,w4,w5] [q17,q92,q295,q352] [n221,n223,n227,n216,n235,n234] (by decide +kernel)
def v122 : Closed T 9 := rotateClosed n228 auto1 auto1ok
def v123 : Closed T 9 := rotateClosed n236 auto1 auto1ok
def v124 : Closed T 9 := rotateClosed n233 auto1 auto1ok
def n237 := cc 10 [w0,w1,w2,w3,w116,w4,w5] [q92,q295] [n228,v122,n236,v123,n201,n217,n233,v124,n222] (by decide +kernel)
def n238 := cc 8 [w0,w134,w1,w2,w3,w4,w5] [q8,q20,q72,q136,q212,q352] [] (by decide +kernel)
def n239 := cc 8 [w0,w1,w2,w136,w3,w4,w5] [q44,q92,q167,q351,q352,q392] [] (by decide +kernel)
def n240 := cc 8 [w137,w0,w1,w2,w3,w4,w5] [q92,q176,q207,q352,q407] [] (by decide +kernel)
def n241 := cc 8 [w140,w0,w1,w2,w3,w4,w5] [q20,q44,q62,q115,q385] [] (by decide +kernel)
def v125 : Closed T 8 := rotateClosed n241 auto3 auto3ok
def v126 : Closed T 8 := rotateClosed n238 auto1 auto1ok
def n242 := cc 9 [w0,w1,w135,w2,w3,w4,w5] [q19,q126,q134,q207,q343,q351,q420] [v125,n240,v126,n239] (by decide +kernel)
def n243 := cc 8 [w142,w0,w1,w2,w3,w4,w5] [q8,q17,q134,q245,q355] [] (by decide +kernel)
def n244 := cc 8 [w0,w1,w144,w2,w3,w4,w5] [q44,q106,q134,q351,q352,q355] [] (by decide +kernel)
def n245 := cc 8 [w146,w0,w1,w2,w3,w4,w5] [q8,q62,q92,q176,q352,q420] [] (by decide +kernel)
def v127 : Closed T 8 := rotateClosed n245 auto3 auto3ok
def v128 : Closed T 8 := rotateClosed n244 auto1 auto1ok
def n246 := cc 9 [w141,w0,w1,w2,w3,w4,w5] [q8,q19,q92,q186,q344,q351,q355] [n241,v127,n243,v128] (by decide +kernel)
def n247 := cc 7 [w0,w6,w9,w3,w4,w147] [q23,q96,q385] [] (by decide +kernel)
def n248 := cc 8 [w0,w6,w1,w2,w3,w4,w147] [q20,q93,q136,q351,q352] [n247] (by decide +kernel)
def n249 := cc 8 [w0,w1,w2,w9,w3,w4,w147] [q44,q106,q167,q351,q352] [n247] (by decide +kernel)
def n250 := cc 8 [w12,w0,w1,w2,w3,w4,w147] [q20,q62,q115,q176,q351,q352] [] (by decide +kernel)
def v129 : Closed T 8 := rotateClosed n250 auto1 auto1ok
def n251 := cc 9 [w0,w1,w2,w3,w4,w147] [q19,q92,q134] [n250,v129,n248,n249] (by decide +kernel)
def n252 := cc 8 [w0,w148,w1,w149,w2,w3,w4] [q54,q111,q134,q351,q352,q355,q361] [] (by decide +kernel)
def n253 := cc 8 [w151,w0,w1,w2,w3,w150,w5] [q10,q69,q187,q351,q352,q353,q420,q436] [] (by decide +kernel)
def n254 := cc 7 [w0,w148,w6,w9,w3,w4] [q8,q23,q96,q351] [] (by decide +kernel)
def n255 := cc 8 [w0,w148,w6,w1,w2,w3,w4] [q8,q17,q20,q93,q354,q355] [n254] (by decide +kernel)
def n256 := cc 8 [w0,w148,w1,w2,w9,w3,w4] [q44,q106,q134,q351,q352,q354,q355] [n254] (by decide +kernel)
def n257 := cc 8 [w12,w0,w148,w1,w2,w3,w4] [q8,q62,q115,q352,q354,q355] [] (by decide +kernel)
def v130 : Closed T 8 := rotateClosed n253 auto2 auto2ok
def v131 : Closed T 8 := rotateClosed n253 auto3 auto3ok
def v132 : Closed T 8 := rotateClosed n257 auto1 auto1ok
def v133 : Closed T 8 := rotateClosed n252 auto1 auto1ok
def n258 := cc 9 [w0,w148,w1,w2,w3,w4] [q19,q92,q355] [v130,v131,n257,v132,n255,n252,v133,n256] (by decide +kernel)
def n259 := cc 8 [w0,w1,w149,w2,w3,w4,w5] [q54,q111,q196,q351,q352,q355,q361] [] (by decide +kernel)
def n260 := cc 8 [w151,w0,w1,w2,w3,w4,w5] [q8,q69,q187,q352,q420,q436] [] (by decide +kernel)
def n261 := cc 7 [w0,w148,w6,w9,w3,w4,w5] [q8,q96,q141,q351,q364] [] (by decide +kernel)
def n262 := cc 8 [w0,w148,w6,w1,w2,w3,w4,w5] [q8,q17,q20,q93,q136,q354,q360] [n261] (by decide +kernel)
def n263 := cc 8 [w0,w148,w1,w2,w9,w3,w4,w5] [q44,q106,q167,q351,q352,q354,q366] [n261] (by decide +kernel)
def n264 := cc 8 [w12,w0,w148,w1,w2,w3,w4,w5] [q8,q62,q115,q176,q352,q354,q368] [] (by decide +kernel)
def v134 : Closed T 8 := rotateClosed n260 auto2 auto2ok
def v135 : Closed T 8 := rotateClosed n260 auto3 auto3ok
def v136 : Closed T 8 := rotateClosed n264 auto1 auto1ok
def v137 : Closed T 8 := rotateClosed n259 auto1 auto1ok
def n265 := cc 9 [w0,w148,w1,w2,w3,w4,w5] [q19,q92,q134,q355] [v134,v135,n264,v136,n262,n263,n259,v137] (by decide +kernel)
def n266 := cc 9 [w132,w138,w1,w2,w4,w5] [q92,q134,q351] [n195] (by decide +kernel)
def n267 := cc 8 [w0,w152,w1,w2,w3,w4,w5] [q17,q97,q136,q207,q352,q420] [] (by decide +kernel)
def v138 : Closed T 7 := rotateClosed n254 auto2 auto2ok
def v139 : Closed T 7 := rotateClosed n261 auto2 auto2ok
def v140 : Closed T 7 := rotateClosed n247 auto2 auto2ok
def n268 := cc 8 [w132,w0,w6,w9,w3,w4,w5] [q23,q96,q141,q207,q351] [v138,v139,v140] (by decide +kernel)
def v141 : Closed T 8 := rotateClosed n243 auto2 auto2ok
def v142 : Closed T 8 := rotateClosed n255 auto2 auto2ok
def v143 : Closed T 8 := rotateClosed n262 auto2 auto2ok
def v144 : Closed T 8 := rotateClosed n248 auto2 auto2ok
def n269 := cc 9 [w132,w0,w6,w1,w2,w3,w4,w5] [q92,q93,q136,q207,q218,q293,q351] [n268,v141,v142,v143,v144,n267] (by decide +kernel)
def n270 := cc 8 [w153,w0,w1,w2,w3,w4,w5] [q44,q106,q134,q351,q352,q355] [] (by decide +kernel)
def v145 : Closed T 8 := rotateClosed n270 auto2 auto2ok
def v146 : Closed T 8 := rotateClosed n256 auto2 auto2ok
def v147 : Closed T 8 := rotateClosed n263 auto2 auto2ok
def v148 : Closed T 8 := rotateClosed n249 auto2 auto2ok
def n271 := cc 9 [w132,w0,w1,w2,w9,w3,w4,w5] [q44,q106,q167,q228,q293,q351,q352] [n268,v145,v146,v147,v148,n239] (by decide +kernel)
def n272 := cc 8 [w154,w0,w1,w2,w3,w4,w5] [q8,q62,q119,q176,q351,q352,q420] [] (by decide +kernel)
def v149 : Closed T 8 := rotateClosed n241 auto2 auto2ok
def v150 : Closed T 8 := rotateClosed n257 auto2 auto2ok
def v151 : Closed T 8 := rotateClosed n264 auto2 auto2ok
def v152 : Closed T 8 := rotateClosed n250 auto2 auto2ok
def n273 := cc 9 [w132,w12,w0,w1,w2,w3,w4,w5] [q115,q176,q207,q293,q352] [v149,v150,v151,v152,n272] (by decide +kernel)
def n274 := cc 8 [w0,w1,w155,w2,w3,w4,w5] [q17,q126,q154,q207,q352] [] (by decide +kernel)
def n275 := cc 9 [w132,w0,w14,w1,w2,w3,w4,w5] [q92,q154,q207,q218,q343,q352,q420] [n274] (by decide +kernel)
def n276 := cc 8 [w156,w0,w1,w2,w3,w4,w5] [q8,q84,q101,q203,q351,q352] [] (by decide +kernel)
def n277 := cc 9 [w132,w15,w0,w1,w2,w3,w4,w5] [q92,q203,q207,q343,q351,q352,q420] [n276] (by decide +kernel)
def v153 : Closed T 9 := rotateClosed n273 auto1 auto1ok
def v154 : Closed T 9 := rotateClosed n277 auto1 auto1ok
def v155 : Closed T 9 := rotateClosed n275 auto1 auto1ok
def v156 : Closed T 9 := rotateClosed n246 auto2 auto2ok
def v157 : Closed T 9 := rotateClosed n246 auto3 auto3ok
def v158 : Closed T 9 := rotateClosed n258 auto2 auto2ok
def v159 : Closed T 9 := rotateClosed n265 auto2 auto2ok
def v160 : Closed T 9 := rotateClosed n242 auto1 auto1ok
def v161 : Closed T 9 := rotateClosed n251 auto2 auto2ok
def n278 := cc 10 [w132,w0,w1,w2,w3,w4,w5] [q19,q92,q134] [n273,v153,n277,v154,n266,n269,n275,v155,n271,v156,v157,v158,v159,n242,v160,v161] (by decide +kernel)
def n279 := cc 7 [w157,w6,w9,w3,w158,w5] [q141,q250,q375] [] (by decide +kernel)
def n280 := cc 8 [w157,w6,w1,w2,w3,w158,w5] [q0,q11,q136,q246,q375] [n279] (by decide +kernel)
def n281 := cc 8 [w157,w1,w2,w9,w3,w158,w5] [q0,q11,q167,q263] [n279] (by decide +kernel)
def n282 := cc 8 [w12,w157,w1,w2,w3,w158,w5] [q20,q44,q176,q277,q375] [] (by decide +kernel)
def v162 : Closed T 8 := rotateClosed n282 auto1 auto1ok
def n283 := cc 9 [w157,w1,w2,w3,w158,w5] [q134,q229] [n282,v162,n280,n281] (by decide +kernel)
def n284 := cc 8 [w157,w0,w6,w9,w3,w4,w5] [q0,q23,q96,q141,q249,q375] [n279] (by decide +kernel)
def n285 := cc 9 [w157,w0,w6,w1,w2,w3,w4,w5] [q0,q11,q20,q93,q136,q245] [n284,n280] (by decide +kernel)
def n286 := cc 9 [w157,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q19,q106,q167,q228,q420] [n284,n281] (by decide +kernel)
def n287 := cc 9 [w12,w157,w0,w1,w2,w3,w4,w5] [q0,q8,q11,q19,q93,q115,q176,q228] [n282] (by decide +kernel)
def v163 : Closed T 9 := rotateClosed n287 auto1 auto1ok
def n288 := cc 10 [w157,w0,w1,w2,w3,w4,w5] [q19,q92,q134,q228] [n287,v163,n285,n286,n283] (by decide +kernel)
def n289 := cc 7 [w159,w0,w1,w2,w3,w160] [q8,q24,q329,q375] [] (by decide +kernel)
def n290 := cc 8 [w159,w0,w1,w2,w3,w158,w5] [q8,q17,q24,q329,q420] [n289] (by decide +kernel)
def n291 := cc 8 [w0,w161,w1,w2,w3,w4,w5] [q8,q20,q72,q329] [] (by decide +kernel)
def n292 := cc 8 [w162,w0,w1,w2,w3,w4,w5] [q8,q20,q72,q329] [] (by decide +kernel)
def n293 := cc 7 [w0,w6,w163,w3,w4,w5] [q8,q96,q250,q332] [] (by decide +kernel)
def n294 := cc 7 [w164,w0,w6,w3,w4,w5] [q23,q332,q375] [] (by decide +kernel)
def n295 := cc 7 [w0,w6,w9,w3,w166,w5] [q141,q207,q332,q385] [] (by decide +kernel)
def n296 := cc 7 [w167,w0,w6,w9,w3,w4] [q23,q141,q375] [] (by decide +kernel)
def v164 : Closed T 7 := rotateClosed n295 auto2 auto2ok
def n297 := cc 8 [w0,w6,w9,w3,w4,w158,w5] [q8,q23,q214,q332] [n296,n294,n279,n293,v164] (by decide +kernel)
def n298 := cc 7 [w0,w6,w169,w3,w4,w5] [q23,q332,q375] [] (by decide +kernel)
def v165 : Closed T 7 := rotateClosed n298 auto1 auto1ok
def n299 := cc 8 [w0,w6,w170,w2,w3,w4,w5] [q8,q20,q72,q329,q352] [v165] (by decide +kernel)
def n300 := cc 8 [w171,w0,w6,w1,w3,w4,w5] [q20,q329,q351,q352,q375] [n294] (by decide +kernel)
def v166 : Closed T 7 := rotateClosed n289 auto2 auto2ok
def n301 := cc 8 [w0,w6,w1,w2,w3,w166,w5] [q136,q207,q218,q329] [v166,n295] (by decide +kernel)
def n302 := cc 8 [w167,w0,w6,w1,w2,w3,w4] [q8,q17,q20,q93,q136] [n296] (by decide +kernel)
def v167 : Closed T 8 := rotateClosed n300 auto1 auto1ok
def v168 : Closed T 8 := rotateClosed n299 auto1 auto1ok
def v169 : Closed T 8 := rotateClosed n301 auto2 auto2ok
def n303 := cc 9 [w0,w6,w1,w2,w3,w4,w158,w5] [q8,q17,q20,q329] [n302,n300,v167,n290,n292,n280,n291,n299,v168,v169,n297] (by decide +kernel)
def n304 := cc 8 [w0,w1,w2,w163,w3,w4,w5] [q8,q17,q44,q263,q333,q375] [n293] (by decide +kernel)
def n305 := cc 8 [w164,w0,w1,w2,w3,w4,w5] [q44,q333,q351,q352] [n294] (by decide +kernel)
def n306 := cc 8 [w0,w1,w2,w9,w3,w166,w5] [q44,q207,q218,q333,q385] [n295] (by decide +kernel)
def n307 := cc 8 [w167,w0,w1,w2,w9,w3,w4] [q8,q17,q44,q106,q167,q375] [n296] (by decide +kernel)
def v170 : Closed T 8 := rotateClosed n306 auto2 auto2ok
def n308 := cc 9 [w0,w1,w2,w9,w3,w4,w158,w5] [q44,q214,q223,q333] [n307,n305,n281,n297,n304,v170] (by decide +kernel)
def n309 := cc 8 [w172,w0,w1,w2,w3,w4,w5] [q20,q62,q334,q352] [] (by decide +kernel)
def n310 := cc 8 [w0,w1,w173,w2,w3,w4,w5] [q20,q44,q72,q336,q375] [] (by decide +kernel)
def n311 := cc 8 [w12,w0,w1,w168,w3,w4,w5] [q20,q44,q62,q334,q375] [] (by decide +kernel)
def n312 := cc 8 [w12,w171,w0,w1,w3,w4,w5] [q20,q62,q334,q351,q352] [] (by decide +kernel)
def n313 := cc 8 [w12,w0,w1,w2,w3,w166,w5] [q20,q44,q62,q334,q385] [] (by decide +kernel)
def n314 := cc 8 [w167,w12,w0,w1,w2,w3,w4] [q20,q44,q62,q176,q375] [] (by decide +kernel)
def v171 : Closed T 8 := rotateClosed n313 auto2 auto2ok
def v172 : Closed T 8 := rotateClosed n310 auto1 auto1ok
def n315 := cc 9 [w12,w0,w1,w2,w3,w4,w158,w5] [q8,q62,q223,q334] [n314,n309,n312,n282,n311,v171,v172] (by decide +kernel)
def n316 := cc 8 [w0,w1,w2,w169,w3,w4,w5] [q17,q44,q62,q333,q351] [n298] (by decide +kernel)
def n317 := cc 8 [w175,w0,w1,w2,w3,w4,w5] [q20,q44,q62,q334,q385] [] (by decide +kernel)
def v173 : Closed T 8 := rotateClosed n311 auto1 auto1ok
def v174 : Closed T 8 := rotateClosed n317 auto3 auto3ok
def v175 : Closed T 8 := rotateClosed n316 auto1 auto1ok
def n318 := cc 9 [w0,w170,w1,w2,w3,w4,w5] [q8,q19,q214,q328] [n309,v173,v174,n291,n299,v175] (by decide +kernel)
def n319 := cc 8 [w0,w1,w176,w2,w3,w4,w5] [q20,q72,q336,q351,q352] [] (by decide +kernel)
def n320 := cc 8 [w0,w178,w1,w2,w3,w4,w5] [q20,q329,q352,q375] [] (by decide +kernel)
def v176 : Closed T 8 := rotateClosed n320 auto2 auto2ok
def n321 := cc 9 [w171,w0,w1,w2,w3,w4,w5] [q17,q19,q328,q352] [n305,n309,n312,n300,v176,n319] (by decide +kernel)
def v177 : Closed T 8 := rotateClosed n313 auto1 auto1ok
def n322 := cc 9 [w0,w1,w2,w3,w166,w5] [q19,q328] [n313,v177,n301,n306] (by decide +kernel)
def v178 : Closed T 8 := rotateClosed n314 auto1 auto1ok
def n323 := cc 9 [w167,w0,w1,w2,w3,w4] [q19,q92,q134] [n314,v178,n302,n307] (by decide +kernel)
def v179 : Closed T 9 := rotateClosed n315 auto1 auto1ok
def v180 : Closed T 9 := rotateClosed n321 auto1 auto1ok
def v181 : Closed T 9 := rotateClosed n318 auto1 auto1ok
def v182 : Closed T 9 := rotateClosed n322 auto2 auto2ok
def n324 := cc 10 [w0,w1,w2,w3,w4,w158,w5] [q19,q328] [n323,n315,v179,n321,v180,n283,n303,n318,v181,n308,v182] (by decide +kernel)
def n325 := cc 7 [w0,w6,w9,w180,w4,w5] [q23,q141,q375] [] (by decide +kernel)
def n326 := cc 8 [w0,w6,w1,w2,w180,w4,w5] [q20,q93,q136,q351,q352] [n325] (by decide +kernel)
def n327 := cc 8 [w0,w1,w2,w9,w180,w4,w5] [q44,q106,q167,q351,q352] [n325] (by decide +kernel)
def n328 := cc 8 [w12,w0,w1,w2,w180,w4,w5] [q20,q62,q115,q176,q351,q352] [] (by decide +kernel)
def v183 : Closed T 8 := rotateClosed n328 auto1 auto1ok
def n329 := cc 9 [w0,w1,w2,w180,w4,w5] [q19,q92,q134] [n328,v183,n326,n327] (by decide +kernel)
def n330 := cc 7 [w182,w6,w9,w3,w4,w5] [q0,q141,q249,q385] [] (by decide +kernel)
def n331 := cc 8 [w182,w6,w1,w2,w3,w4,w5] [q0,q11,q136,q245,q385] [n330] (by decide +kernel)
def n332 := cc 8 [w182,w1,w2,w9,w3,w4,w5] [q0,q11,q167,q262,q399] [n330] (by decide +kernel)
def n333 := cc 8 [w12,w182,w1,w2,w3,w4,w5] [q136,q167,q176,q276,q385] [] (by decide +kernel)
def v184 : Closed T 8 := rotateClosed n333 auto1 auto1ok
def n334 := cc 9 [w182,w1,w2,w3,w4,w5] [q134,q228] [n333,v184,n331,n332] (by decide +kernel)
def n335 := cc 8 [w0,w184,w1,w2,w3,w4,w5] [q136,q245,q352,q375] [] (by decide +kernel)
def n336 := cc 8 [w0,w1,w2,w186,w3,w4,w5] [q167,q176,q262,q351] [] (by decide +kernel)
def n337 := cc 8 [w187,w0,w1,w2,w3,w4,w5] [q20,q176,q276,q351,q352] [] (by decide +kernel)
def n338 := cc 8 [w189,w0,w1,w2,w3,w4,w5] [q93,q115,q176,q276,q352] [] (by decide +kernel)
def v185 : Closed T 8 := rotateClosed n338 auto3 auto3ok
def v186 : Closed T 8 := rotateClosed n335 auto1 auto1ok
def n339 := cc 9 [w0,w1,w185,w2,w3,w4,w5] [q134,q215,q228,q351] [v185,n337,v186,n336] (by decide +kernel)
def n340 := cc 8 [w0,w191,w1,w2,w3,w4,w5] [q0,q93,q136,q245,q375] [] (by decide +kernel)
def n341 := cc 8 [w0,w1,w2,w193,w3,w4,w5] [q11,q123,q167,q262] [] (by decide +kernel)
def n342 := cc 8 [w195,w0,w1,w2,w3,w4,w5] [q44,q136,q176,q276,q385] [] (by decide +kernel)
def v187 : Closed T 8 := rotateClosed n342 auto3 auto3ok
def v188 : Closed T 8 := rotateClosed n341 auto1 auto1ok
def n343 := cc 9 [w0,w190,w1,w2,w3,w4,w5] [q0,q8,q92,q134,q228] [n338,v187,n340,v188] (by decide +kernel)
def n344 := cc 8 [w0,w196,w1,w2,w3,w4,w5] [q136,q208,q245,q385] [] (by decide +kernel)
def v189 : Closed T 7 := rotateClosed n325 auto2 auto2ok
def n345 := cc 8 [w181,w0,w6,w9,w3,w4,w5] [q141,q208,q215,q249,q428] [n330,v189] (by decide +kernel)
def v190 : Closed T 8 := rotateClosed n340 auto2 auto2ok
def v191 : Closed T 8 := rotateClosed n326 auto2 auto2ok
def n346 := cc 9 [w181,w0,w6,w1,w2,w3,w4,w5] [q136,q215,q224,q245,q426] [n345,n331,v190,v191,n344] (by decide +kernel)
def n347 := cc 8 [w0,w1,w2,w197,w3,w4,w5] [q0,q115,q167,q262] [] (by decide +kernel)
def n348 := cc 8 [w181,w0,w1,w2,w198,w3,w4] [q167,q208,q266,q352,q355,q399] [] (by decide +kernel)
def v192 : Closed T 8 := rotateClosed n347 auto2 auto2ok
def v193 : Closed T 8 := rotateClosed n327 auto2 auto2ok
def n349 := cc 9 [w181,w0,w1,w2,w9,w3,w4,w5] [q167,q208,q219,q262,q432] [n345,n348,n332,v192,v193,n336] (by decide +kernel)
def n350 := cc 8 [w199,w0,w1,w2,w3,w4,w5] [q136,q167,q176,q276,q385] [] (by decide +kernel)
def v194 : Closed T 8 := rotateClosed n338 auto2 auto2ok
def v195 : Closed T 8 := rotateClosed n328 auto2 auto2ok
def n351 := cc 9 [w181,w12,w0,w1,w2,w3,w4,w5] [q176,q215,q219,q276,q434] [v194,n333,v195,n350] (by decide +kernel)
def v196 : Closed T 9 := rotateClosed n351 auto1 auto1ok
def v197 : Closed T 9 := rotateClosed n343 auto2 auto2ok
def v198 : Closed T 9 := rotateClosed n343 auto3 auto3ok
def v199 : Closed T 9 := rotateClosed n339 auto1 auto1ok
def v200 : Closed T 9 := rotateClosed n329 auto2 auto2ok
def n352 := cc 10 [w181,w0,w1,w2,w3,w4,w5] [q134,q228,q420] [n351,v196,n346,n349,n334,v197,v198,n339,v199,v200] (by decide +kernel)
def n353 := cc 8 [w0,w202,w1,w2,w3,w4,w5] [q20,q296,q352,q375,q426] [] (by decide +kernel)
def n354 := cc 8 [w0,w1,w2,w204,w3,w4,w5] [q44,q62,q268,q309,q351,q432] [] (by decide +kernel)
def n355 := cc 8 [w205,w0,w1,w2,w3,w4,w5] [q20,q62,q271,q314,q351,q352,q434] [] (by decide +kernel)
def n356 := cc 8 [w208,w0,w1,w2,w3,w4,w5] [q20,q62,q115,q184,q352,q368] [] (by decide +kernel)
def v201 : Closed T 8 := rotateClosed n356 auto3 auto3ok
def v202 : Closed T 8 := rotateClosed n353 auto1 auto1ok
def n357 := cc 9 [w0,w1,w203,w2,w3,w4,w5] [q19,q207,q270,q295,q351,q420] [v201,n355,v202,n354] (by decide +kernel)
def n358 := cc 8 [w210,w0,w1,w2,w3,w4,w5] [q8,q20,q72,q93,q134,q149,q355,q360] [] (by decide +kernel)
def n359 := cc 8 [w0,w1,w212,w2,w3,w4,w5] [q17,q44,q62,q106,q191,q351,q366] [] (by decide +kernel)
def n360 := cc 8 [w209,w0,w1,w2,w213,w3,w4,w5] [q8,q17,q44,q106,q189,q366] [] (by decide +kernel)
def n361 := cc 8 [w215,w0,w1,w2,w3,w4,w5] [q8,q17,q44,q283,q314,q434] [] (by decide +kernel)
def n362 := cc 8 [w215,w0,w1,w214,w2,w3,w4,w5] [q17,q44,q207,q283,q314,q434] [] (by decide +kernel)
def n363 := cc 8 [w209,w0,w1,w2,w9,w3,w4,w5] [q0,q8,q17,q44,q106,q167,q187,q366] [] (by decide +kernel)
def n364 := cc 8 [w12,w211,w0,w1,w2,w3,w4,w5] [q8,q44,q62,q115,q176,q190,q368,q376] [] (by decide +kernel)
def v203 : Closed T 8 := rotateClosed n364 auto1 auto1ok
def v204 : Closed T 8 := rotateClosed n362 auto3 auto3ok
def v205 : Closed T 8 := rotateClosed n361 auto3 auto3ok
def v206 : Closed T 8 := rotateClosed n359 auto1 auto1ok
def n365 := cc 9 [w209,w0,w1,w2,w3,w4,w5] [q8,q19,q92,q187,q355] [n356,v203,v204,v205,n358,n360,n363,v206] (by decide +kernel)
def n366 := cc 8 [w0,w1,w217,w2,w3,w4,w5] [q54,q111,q198,q351,q352,q355,q362] [] (by decide +kernel)
def n367 := cc 8 [w219,w0,w1,w2,w3,w4,w5] [q8,q255,q318,q352,q437] [] (by decide +kernel)
def n368 := cc 7 [w0,w216,w6,w9,w3,w4,w5] [q8,q23,q96,q216] [] (by decide +kernel)
def n369 := cc 8 [w0,w216,w6,w1,w2,w3,w4,w5] [q8,q17,q20,q93,q360,q369,q420] [n368] (by decide +kernel)
def n370 := cc 8 [w0,w216,w1,w2,w9,w3,w4,w5] [q8,q17,q44,q106,q167,q216,q352,q355,q369] [n368] (by decide +kernel)
def n371 := cc 8 [w12,w0,w216,w1,w2,w3,w4,w5] [q8,q17,q44,q62,q115,q352,q368,q369] [] (by decide +kernel)
def v207 : Closed T 8 := rotateClosed n367 auto2 auto2ok
def v208 : Closed T 8 := rotateClosed n367 auto3 auto3ok
def v209 : Closed T 8 := rotateClosed n371 auto1 auto1ok
def v210 : Closed T 8 := rotateClosed n366 auto1 auto1ok
def n372 := cc 9 [w0,w216,w1,w2,w3,w4,w5] [q19,q92,q134,q355] [v207,v208,n371,v209,n369,n370,n366,v210] (by decide +kernel)
def n373 := cc 8 [w0,w220,w1,w2,w3,w4,w5] [q20,q72,q207,q248,q296,q426] [] (by decide +kernel)
def n374 := cc 7 [w221,w0,w6,w9,w3,w4,w5] [q8,q23,q96,q141,q364,q376] [] (by decide +kernel)
def n375 := cc 7 [w200,w0,w6,w222,w9,w4,w5] [q23,q207,q249,q301,q351,q387] [] (by decide +kernel)
def v211 : Closed T 7 := rotateClosed n374 auto2 auto2ok
def v212 : Closed T 7 := rotateClosed n368 auto2 auto2ok
def n376 := cc 8 [w200,w0,w6,w9,w3,w4,w5] [q23,q207,q249,q301,q351,q385,q428] [n375,v211,v212] (by decide +kernel)
def v213 : Closed T 8 := rotateClosed n358 auto2 auto2ok
def v214 : Closed T 8 := rotateClosed n369 auto2 auto2ok
def n377 := cc 9 [w200,w0,w6,w1,w2,w3,w4,w5] [q20,q207,q218,q245,q296,q355,q426] [n376,v213,v214,n373] (by decide +kernel)
def n378 := cc 8 [w221,w0,w1,w2,w3,w4,w5] [q0,q8,q44,q106,q174,q366] [] (by decide +kernel)
def n379 := cc 8 [w221,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q44,q106,q174,q366] [n374] (by decide +kernel)
def n380 := cc 8 [w200,w0,w1,w2,w222,w9,w4,w5] [q44,q207,q208,q218,q262,q309,q352] [n375] (by decide +kernel)
def v215 : Closed T 8 := rotateClosed n363 auto2 auto2ok
def v216 : Closed T 8 := rotateClosed n363 auto3 auto3ok
def v217 : Closed T 8 := rotateClosed n379 auto2 auto2ok
def v218 : Closed T 8 := rotateClosed n378 auto2 auto2ok
def v219 : Closed T 8 := rotateClosed n370 auto2 auto2ok
def n381 := cc 9 [w200,w0,w1,w2,w9,w3,w4,w5] [q44,q207,q208,q218,q228,q262,q309,q352,q432] [n376,n380,v215,v216,v217,v218,v219,n354] (by decide +kernel)
def n382 := cc 8 [w223,w0,w1,w2,w3,w4,w5] [q44,q62,q207,q280,q314,q434] [] (by decide +kernel)
def v220 : Closed T 8 := rotateClosed n356 auto2 auto2ok
def v221 : Closed T 8 := rotateClosed n364 auto2 auto2ok
def v222 : Closed T 8 := rotateClosed n371 auto2 auto2ok
def n383 := cc 9 [w200,w12,w0,w1,w2,w3,w4,w5] [q44,q62,q207,q276,q314,q352,q385,q434] [v220,v221,v222,n382] (by decide +kernel)
def v223 : Closed T 9 := rotateClosed n383 auto1 auto1ok
def v224 : Closed T 9 := rotateClosed n365 auto2 auto2ok
def v225 : Closed T 9 := rotateClosed n365 auto3 auto3ok
def v226 : Closed T 9 := rotateClosed n372 auto2 auto2ok
def v227 : Closed T 9 := rotateClosed n357 auto1 auto1ok
def n384 := cc 10 [w200,w0,w1,w2,w3,w4,w5] [q19,q228,q295,q420] [n383,v223,n377,n381,v224,v225,v226,n357,v227] (by decide +kernel)
def n385 := cc 8 [w0,w6,w1,w69,w2,w3,w4,w5] [q8,q20,q54,q136,q176,q214,q241,q245,q352] [] (by decide +kernel)
def n386 := cc 7 [w0,w225,w9,w3,w4,w5] [q8,q141,q352,q375] [] (by decide +kernel)
def n387 := cc 8 [w0,w1,w224,w9,w3,w4,w5] [q0,q167,q219,q355] [n386] (by decide +kernel)
def n388 := cc 8 [w12,w0,w69,w2,w3,w4,w5] [q11,q67,q136,q176,q208,q214,q215] [n91] (by decide +kernel)
def n389 := cc 8 [w12,w0,w1,w69,w2,w3,w4,w5] [q8,q67,q136,q176,q214,q215,q241,q276,q375] [] (by decide +kernel)
def n390 := cc 7 [w0,w225,w1,w22,w224,w3,w4] [q4,q136,q219,q223,q360] [] (by decide +kernel)
def n391 := cc 7 [w76,w0,w72,w69,w2,w3,w4] [q12,q208,q214,q368] [] (by decide +kernel)
def n392 := cc 7 [w0,w14,w1,w22,w224,w3,w4] [q39,q156,q199,q223,q259,q356] [] (by decide +kernel)
def n393 := cc 7 [w15,w0,w72,w69,w2,w3,w4] [q12,q32,q214,q256,q367] [] (by decide +kernel)
def v228 : Closed T 7 := rotateClosed n391 auto2 auto2ok
def v229 : Closed T 7 := rotateClosed n393 auto2 auto2ok
def v230 : Closed T 7 := rotateClosed n390 auto3 auto3ok
def v231 : Closed T 7 := rotateClosed n392 auto3 auto3ok
def n394 := cc 8 [w0,w14,w2,w3,w111,w5] [q0,q29,q217,q228,q420] [n180,v228,v229,v230,v231] (by decide +kernel)
def n395 := cc 8 [w0,w14,w1,w2,w3,w111,w5] [q0,q207,q217,q228] [n180] (by decide +kernel)
def n396 := cc 8 [w0,w225,w1,w2,w3,w4,w5] [q0,q136,q207,q212,q352] [n386] (by decide +kernel)
def n397 := cc 8 [w0,w225,w1,w2,w224,w3,w4,w5] [q0,q8,q136,q219,q223] [n390] (by decide +kernel)
def n398 := cc 8 [w0,w1,w2,w226,w3,w4,w5] [q19,q92,q167,q208,q352,q392] [] (by decide +kernel)
def n399 := cc 8 [w76,w0,w1,w2,w3,w4,w5] [q20,q176,q208,q223] [] (by decide +kernel)
def n400 := cc 8 [w76,w0,w1,w69,w2,w3,w4,w5] [q11,q136,q176,q208,q214] [n391,n111] (by decide +kernel)
def n401 := cc 8 [w228,w0,w1,w2,w3,w4,w5] [q8,q19,q262,q276,q385] [] (by decide +kernel)
def n402 := cc 7 [w41,w0,w2,w3,w111,w4,w5] [q4,q40,q207,q247,q261,q317,q385] [] (by decide +kernel)
def v232 : Closed T 7 := rotateClosed n402 auto3 auto3ok
def n403 := cc 8 [w0,w14,w1,w2,w224,w3,w4,w5] [q0,q8,q26,q57,q113,q154,q214,q222,q223,q242,q420] [v232,n392] (by decide +kernel)
def n404 := cc 8 [w15,w0,w1,w69,w2,w3,w4,w5] [q11,q54,q84,q203,q214,q221,q241] [n393] (by decide +kernel)
def v233 : Closed T 8 := rotateClosed n401 auto3 auto3ok
def v234 : Closed T 8 := rotateClosed n192 auto2 auto2ok
def v235 : Closed T 8 := rotateClosed n397 auto1 auto1ok
def v236 : Closed T 8 := rotateClosed n396 auto1 auto1ok
def v237 : Closed T 8 := rotateClosed n403 auto1 auto1ok
def v238 : Closed T 8 := rotateClosed n395 auto2 auto2ok
def v239 : Closed T 8 := rotateClosed n394 auto2 auto2ok
def v240 : Closed T 8 := rotateClosed n387 auto1 auto1ok
def n405 := cc 9 [w0,w1,w69,w2,w3,w4,w5] [q19,q54,q111,q134,q208,q214,q392,q420] [v233,v234,n389,n388,n400,n399,n404,n385,v235,v236,v237,v238,v239,n112,n398,v240] (by decide +kernel)
def n406 := cc 7 [w229,w0,w9,w3,w4,w5] [q8,q208,q209,q249] [] (by decide +kernel)
def n407 := cc 8 [w229,w0,w1,w2,w3,w4,w5] [q8,q17,q134,q245,q355] [n406] (by decide +kernel)
def n408 := cc 8 [w0,w1,w231,w2,w3,w4,w5] [q0,q17,q62,q217,q262] [] (by decide +kernel)
def n409 := cc 8 [w233,w0,w1,w2,w3,w4,w5] [q11,q92,q176,q207,q420] [] (by decide +kernel)
def n410 := cc 6 [w62,w232,w0,w9,w3,w4,w5] [q8] [] (by decide +kernel)
def n411 := cc 7 [w62,w232,w0,w1,w2,w3,w4,w5] [q8,q11,q17,q208] [n410] (by decide +kernel)
def n412 := cc 6 [w62,w234,w0,w2,w3,w4,w5] [] [] (by decide +kernel)
def n413 := cc 7 [w62,w19,w0,w2,w9,w3,w4,w5] [q8,q208,q219] [n410,n412] (by decide +kernel)
def n414 := cc 7 [w62,w19,w0,w1,w22,w2,w3,w4] [q8,q37,q134,q219] [] (by decide +kernel)
def n415 := cc 8 [w62,w19,w0,w1,w2,w3,w4,w5] [q8,q11,q17,q19,q166,q208,q219,q235] [n411,n414,n413] (by decide +kernel)
def n416 := cc 8 [w62,w0,w2,w9,w3,w4,w5] [q8,q208,q219,q262,q319] [n406,n413] (by decide +kernel)
def n417 := cc 7 [w12,w0,w236,w3,w4,w5] [] [] (by decide +kernel)
def v241 : Closed T 7 := rotateClosed n417 auto2 auto2ok
def n418 := cc 8 [w62,w12,w0,w2,w3,w4,w5] [q8,q17,q215,q262,q276,q407] [v241] (by decide +kernel)
def n419 := cc 7 [w62,w0,w22,w2,w237,w3,w4,w5] [q261,q319,q355] [] (by decide +kernel)
def n420 := cc 8 [w62,w0,w1,w22,w2,w3,w4,w5] [q8,q17,q166,q208,q215,q219,q226,q258] [n414,n419] (by decide +kernel)
def n421 := cc 8 [w62,w23,w0,w1,w2,w3,w4,w5] [q8,q17,q166,q208,q215,q219,q290] [] (by decide +kernel)
def v242 : Closed T 8 := rotateClosed n409 auto3 auto3ok
def v243 : Closed T 8 := rotateClosed n408 auto1 auto1ok
def n422 := cc 9 [w62,w0,w1,w2,w3,w4,w5] [q8,q19,q134,q208,q228,q318,q355] [n401,n407,n161,n418,n421,n70,n415,n420,n416,v242,v243] (by decide +kernel)
def n423 := cc 8 [w0,w1,w239,w2,w3,w4,w5] [q133,q197,q270,q321,q351,q352,q363] [] (by decide +kernel)
def n424 := cc 8 [w241,w0,w1,w2,w3,w4,w5] [q8,q17,q71,q99,q187,q232,q352,q420] [] (by decide +kernel)
def n425 := cc 7 [w238,w0,w6,w9,w3,w4,w5] [q8,q141,q208,q346,q364] [] (by decide +kernel)
def n426 := cc 8 [w238,w0,w6,w1,w2,w3,w4,w5] [q17,q132,q136,q164,q208,q219,q245,q294,q346,q360] [n425] (by decide +kernel)
def n427 := cc 8 [w238,w0,w1,w2,w9,w3,w4,w5] [q8,q91,q164,q167,q208,q219,q262,q294,q309,q366,q392] [n425] (by decide +kernel)
def n428 := cc 8 [w238,w12,w0,w1,w2,w3,w4,w5] [q8,q132,q164,q176,q208,q219,q245,q276,q294,q314,q368] [] (by decide +kernel)
def v244 : Closed T 8 := rotateClosed n428 auto1 auto1ok
def v245 : Closed T 8 := rotateClosed n424 auto2 auto2ok
def v246 : Closed T 8 := rotateClosed n424 auto3 auto3ok
def v247 : Closed T 8 := rotateClosed n423 auto1 auto1ok
def n429 := cc 9 [w238,w0,w1,w2,w3,w4,w5] [q91,q164,q228,q295,q355] [n428,v244,n426,n427,v245,v246,n423,v247] (by decide +kernel)
def n430 := cc 7 [w19,w243,w1,w2,w3,w4] [q4,q20,q93,q136,q385] [] (by decide +kernel)
def n431 := cc 7 [w19,w6,w9,w3,w4,w242] [q0,q8,q23,q96,q141,q372] [] (by decide +kernel)
def n432 := cc 8 [w19,w6,w1,w2,w3,w4,w242] [q8,q17,q20,q93,q136,q371] [n430,n431] (by decide +kernel)
def n433 := cc 8 [w19,w1,w2,w9,w3,w4,w242] [q0,q11,q44,q106,q373,q399] [n431] (by decide +kernel)
def n434 := cc 8 [w12,w19,w1,w2,w3,w4,w242] [q8,q11,q62,q115,q374,q413] [] (by decide +kernel)
def n435 := cc 7 [w245,w19,w1,w2,w3,w4] [q20,q62,q115,q176,q385] [] (by decide +kernel)
def v248 : Closed T 7 := rotateClosed n435 auto1 auto1ok
def n436 := cc 8 [w19,w246,w1,w2,w3,w4] [q8,q19,q92,q134,q217] [v248,n430] (by decide +kernel)
def v249 : Closed T 8 := rotateClosed n434 auto1 auto1ok
def v250 : Closed T 8 := rotateClosed n436 auto1 auto1ok
def n437 := cc 9 [w19,w1,w2,w3,w4,w242] [q19,q92,q134,q370] [n434,v249,n432,n436,v250,n433] (by decide +kernel)
def n438 := cc 6 [w248,w0,w9,w3,w247,w4,w5] [q45,q107] [] (by decide +kernel)
def n439 := cc 6 [w249,w0,w9,w3,w247,w4,w5] [q45,q107] [] (by decide +kernel)
def n440 := cc 6 [w0,w251,w250,w9,w3,w4,w5] [q108,q141] [] (by decide +kernel)
def n441 := cc 6 [w252,w0,w9,w3,w247,w4,w5] [q107,q254,q310] [] (by decide +kernel)
def n442 := cc 4 [w0,w9,w3,w253,w254] [q375] [] (by decide +kernel)
def n443 := cc 5 [w0,w9,w3,w253,w4,w5] [q375] [n442] (by decide +kernel)
def n444 := cc 5 [w255,w0,w9,w3,w4,w5] [] [] (by decide +kernel)
def v251 : Closed T 5 := rotateClosed n444 auto2 auto2ok
def n445 := cc 6 [w19,w0,w9,w3,w247,w4,w5] [q107,q237,q249,q428] [v251,n443] (by decide +kernel)
def n446 := cc 6 [w0,w250,w9,w3,w254,w4] [q108,q141,q146,q148,q152,q331,q364,q375] [] (by decide +kernel)
def v252 : Closed T 6 := rotateClosed n439 auto2 auto2ok
def v253 : Closed T 6 := rotateClosed n441 auto2 auto2ok
def v254 : Closed T 6 := rotateClosed n438 auto2 auto2ok
def v255 : Closed T 6 := rotateClosed n445 auto2 auto2ok
def n447 := cc 7 [w0,w250,w9,w3,w4,w5] [q0,q46,q108,q141,q142,q215,q299] [v252,v253,v254,v255,n440,n446] (by decide +kernel)
def n448 := cc 7 [w248,w0,w1,w2,w3,w247,w4,w5] [q21,q94,q134] [n438] (by decide +kernel)
def n449 := cc 7 [w249,w0,w1,w2,w3,w247,w4,w5] [q21,q94,q134] [n439] (by decide +kernel)
def n450 := cc 7 [w0,w1,w251,w250,w2,w3,w4,w5] [q95,q138,q420] [n440] (by decide +kernel)
def n451 := cc 7 [w252,w0,w1,w2,w3,w247,w4,w5] [q252,q253,q300,q355] [n441] (by decide +kernel)
def n452 := cc 7 [w0,w1,w256,w250,w2,w3,w4] [q8,q17,q22,q95,q136,q142] [] (by decide +kernel)
def n453 := cc 5 [w0,w1,w2,w3,w253,w254] [] [n442] (by decide +kernel)
def n454 := cc 6 [w0,w1,w2,w3,w253,w4,w5] [q19,q92,q134,q351,q352] [n453,n443] (by decide +kernel)
def n455 := cc 6 [w255,w0,w1,w2,w3,w4,w5] [] [n444] (by decide +kernel)
def v256 : Closed T 6 := rotateClosed n455 auto2 auto2ok
def n456 := cc 7 [w19,w0,w1,w2,w3,w247,w4,w5] [q21,q94,q134,q236,q245,q355,q426] [v256,n445,n454] (by decide +kernel)
def n457 := cc 7 [w0,w1,w250,w2,w3,w254,w4] [q7,q14,q95,q136,q139,q151,q330,q360] [n446] (by decide +kernel)
def v257 : Closed T 7 := rotateClosed n449 auto2 auto2ok
def v258 : Closed T 7 := rotateClosed n451 auto2 auto2ok
def v259 : Closed T 7 := rotateClosed n448 auto2 auto2ok
def v260 : Closed T 7 := rotateClosed n456 auto2 auto2ok
def n458 := cc 8 [w0,w1,w250,w2,w3,w4,w5] [q0,q8,q11,q17,q19,q22,q95,q136,q215,q224,q228,q298,q420] [v257,v258,v259,v260,n450,n452,n457,n447] (by decide +kernel)
def n459 := cc 7 [w0,w6,w250,w9,w3,w4,w5] [q0,q215,q337,q338,q388] [] (by decide +kernel)
def n460 := cc 8 [w0,w6,w1,w250,w2,w3,w4,w5] [q0,q11,q17,q136,q215,q337,q338] [n459] (by decide +kernel)
def n461 := cc 7 [w0,w1,w258,w2,w3,w4,w5] [q95,q118,q125,q138,q228,q422,q424,q425] [] (by decide +kernel)
def n462 := cc 8 [w19,w0,w257,w1,w2,w3,w4,w5] [q8,q17,q19,q93,q138,q235,q245,q422] [n461] (by decide +kernel)
def n463 := cc 8 [w159,w19,w0,w1,w2,w3,w4,w5] [q8,q17,q19,q93,q150,q212,q214,q223,q235,q245,q355,q422] [] (by decide +kernel)
def n464 := cc 4 [w0,w6,w260,w3,w254] [q375] [] (by decide +kernel)
def n465 := cc 5 [w0,w6,w260,w3,w4,w5] [q375] [n464] (by decide +kernel)
def n466 := cc 6 [w0,w6,w9,w3,w259,w4,w5] [q8,q147,q351] [n465,n443] (by decide +kernel)
def n467 := cc 6 [w19,w0,w6,w9,w47,w3,w254] [q23,q96,q147,q148,q237] [] (by decide +kernel)
def n468 := cc 7 [w19,w0,w6,w9,w47,w3,w4,w5] [q8,q96,q141,q207,q249,q364,q428] [n467,n445,v255,n466] (by decide +kernel)
def n469 := cc 7 [w19,w0,w6,w9,w3,w254,w4] [q7,q23,q141,q338] [n467,n446] (by decide +kernel)
def v261 : Closed T 7 := rotateClosed n406 auto2 auto2ok
def v262 : Closed T 7 := rotateClosed n425 auto2 auto2ok
def n470 := cc 8 [w19,w0,w6,w9,w3,w4,w5] [q0,q141,q215,q249,q301,q337,q338,q385] [v261,v262,n468,n469,n431,n459,n447] (by decide +kernel)
def n471 := cc 5 [w261,w0,w1,w2,w3,w254] [] [] (by decide +kernel)
def n472 := cc 6 [w261,w0,w1,w2,w3,w4,w5] [] [n471] (by decide +kernel)
def n473 := cc 7 [w0,w6,w1,w2,w3,w259,w4,w5] [q8,q17,q140,q351,q352] [n472,n466,n454] (by decide +kernel)
def n474 := cc 7 [w19,w0,w6,w1,w2,w47,w3,w254] [q20,q42,q93,q139,q140,q164,q235,q236,q328,q357] [n467] (by decide +kernel)
def n475 := cc 8 [w19,w0,w6,w1,w2,w47,w3,w4,w5] [q8,q19,q93,q136,q164,q207,q235,q245,q357,q360,q422,q426] [n474,n468,n456,v260,n473] (by decide +kernel)
def n476 := cc 8 [w19,w0,w6,w1,w2,w3,w254,w4] [q14,q42,q123,q136,q235,q329,q338,q360,q422] [n474,n469,n457] (by decide +kernel)
def v263 : Closed T 8 := rotateClosed n407 auto2 auto2ok
def v264 : Closed T 8 := rotateClosed n426 auto2 auto2ok
def v265 : Closed T 8 := rotateClosed n385 auto1 auto1ok
def n477 := cc 9 [w19,w0,w6,w1,w2,w3,w4,w5] [q0,q11,q17,q19,q93,q136,q215,q224,q235,q245,q296,q337,q338,q355] [v263,v264,n463,n462,n475,n476,n470,n432,n460,n385,v265,n458] (by decide +kernel)
def n478 := cc 5 [w263,w0,w1,w2,w3,w254] [] [] (by decide +kernel)
def n479 := cc 6 [w263,w0,w1,w2,w3,w4,w5] [] [n478] (by decide +kernel)
def v266 : Closed T 6 := rotateClosed n412 auto2 auto2ok
def v267 : Closed T 6 := rotateClosed n412 auto3 auto3ok
def n480 := cc 7 [w262,w19,w0,w1,w2,w3,w4,w5] [q50,q134,q208,q219,q243,q355] [n479,v266,v267] (by decide +kernel)
def n481 := cc 7 [w262,w0,w1,w2,w3,w254,w5] [q173,q243,q267,q312] [] (by decide +kernel)
def n482 := cc 8 [w262,w0,w1,w2,w3,w4,w5] [q50,q134,q208,q219,q262,q312,q355] [n480,n481] (by decide +kernel)
def n483 := cc 8 [w19,w0,w1,w2,w36,w3,w4,w5] [q0,q11,q19,q106,q170,q214,q394,q422] [] (by decide +kernel)
def n484 := cc 5 [w0,w1,w2,w260,w3,w254] [q134] [n464] (by decide +kernel)
def n485 := cc 6 [w0,w1,w2,w260,w3,w4,w5] [q134,q351,q352] [n465,n484] (by decide +kernel)
def n486 := cc 7 [w0,w1,w2,w9,w3,w259,w4,w5] [q8,q17,q171,q351,q352] [n479,n466,n485] (by decide +kernel)
def n487 := cc 7 [w19,w0,w1,w2,w9,w47,w3,w254] [q42,q44,q106,q164,q171,q172,q235,q243,q328,q357] [n467] (by decide +kernel)
def v268 : Closed T 7 := rotateClosed n413 auto1 auto1ok
def v269 : Closed T 7 := rotateClosed n413 auto2 auto2ok
def v270 : Closed T 7 := rotateClosed n413 auto3 auto3ok
def v271 : Closed T 7 := rotateClosed n480 auto2 auto2ok
def n488 := cc 8 [w19,w0,w1,w2,w9,w47,w3,w4,w5] [q0,q11,q44,q106,q164,q167,q208,q219,q357,q366,q394,q432] [n413,v268,v269,v270,n480,v271,n468,n487,n486] (by decide +kernel)
def v272 : Closed T 7 := rotateClosed n481 auto2 auto2ok
def n489 := cc 8 [w19,w0,w1,w2,w9,w3,w254,w4] [q7,q14,q42,q106,q134,q235,q333,q366,q422] [v272,n469,n487] (by decide +kernel)
def v273 : Closed T 8 := rotateClosed n416 auto2 auto2ok
def v274 : Closed T 8 := rotateClosed n416 auto3 auto3ok
def v275 : Closed T 8 := rotateClosed n482 auto2 auto2ok
def v276 : Closed T 8 := rotateClosed n427 auto2 auto2ok
def n490 := cc 9 [w19,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q19,q44,q106,q167,q235,q262,q309,q355] [v273,v274,v275,v276,n470,n483,n488,n489,n433,n398,n387,v240] (by decide +kernel)
def n491 := cc 6 [w0,w1,w2,w3,w265,w4,w5] [q351] [] (by decide +kernel)
def n492 := cc 7 [w19,w0,w1,w2,w3,w264,w4,w5] [q64,q116,q134,q207,q208,q219,q355,q434] [n491] (by decide +kernel)
def v277 : Closed T 7 := rotateClosed n492 auto2 auto2ok
def n493 := cc 8 [w0,w266,w1,w2,w3,w4,w5] [q0,q8,q11,q65,q117,q176,q215,q228,q420] [v277] (by decide +kernel)
def n494 := cc 8 [w19,w0,w1,w39,w2,w3,w4,w5] [q0,q17,q19,q123,q195,q223,q375,q394,q422] [] (by decide +kernel)
def n495 := cc 6 [w0,w1,w267,w2,w3,w4,w5] [q8] [] (by decide +kernel)
def v278 : Closed T 6 := rotateClosed n495 auto1 auto1ok
def n496 := cc 7 [w12,w0,w1,w2,w3,w259,w4,w5] [q8,q17,q59,q164,q182,q235,q351,q352,q357,q408] [v278,n491] (by decide +kernel)
def n497 := cc 7 [w12,w19,w0,w1,w2,w47,w3,w254] [q42,q62,q115,q164,q182,q235,q328,q357] [] (by decide +kernel)
def n498 := cc 8 [w12,w19,w0,w1,w2,w47,w3,w4,w5] [q0,q8,q19,q115,q164,q176,q207,q208,q357,q368,q408,q434] [n497,n496,n492,v277] (by decide +kernel)
def n499 := cc 8 [w12,w19,w0,w1,w2,w3,w254,w4] [q7,q14,q42,q93,q115,q134,q235,q334,q368] [n497] (by decide +kernel)
def v279 : Closed T 8 := rotateClosed n401 auto2 auto2ok
def v280 : Closed T 8 := rotateClosed n418 auto2 auto2ok
def v281 : Closed T 8 := rotateClosed n428 auto2 auto2ok
def v282 : Closed T 8 := rotateClosed n494 auto1 auto1ok
def n500 := cc 9 [w12,w19,w0,w1,w2,w3,w4,w5] [q0,q8,q11,q19,q62,q115,q136,q176,q215,q235,q276,q314,q355] [v279,v280,v281,n498,n499,n434,n389,n388,v282,n493] (by decide +kernel)
def n501 := cc 8 [w0,w1,w268,w2,w3,w4,w5] [q17,q19,q154,q345,q352] [] (by decide +kernel)
def n502 := cc 7 [w269,w0,w1,w22,w2,w3,w4,w5] [q260,q261,q312] [] (by decide +kernel)
def v283 : Closed T 7 := rotateClosed n419 auto3 auto3ok
def v284 : Closed T 7 := rotateClosed n502 auto3 auto3ok
def n503 := cc 8 [w19,w0,w14,w1,w2,w270,w3,w4,w5] [q106,q123,q157,q214,q223,q356,q422] [v283,v284] (by decide +kernel)
def n504 := cc 7 [w0,w271,w1,w2,w3,w4,w5] [q8,q56,q103,q117,q213,q228] [] (by decide +kernel)
def v285 : Closed T 7 := rotateClosed n504 auto2 auto2ok
def n505 := cc 8 [w41,w0,w1,w2,w47,w3,w4,w5] [q44,q218,q226,q261,q314,q337,q420] [n402,v285] (by decide +kernel)
def n506 := cc 8 [w41,w0,w1,w22,w2,w47,w3,w4,w5] [q215,q216,q226,q260,q261,q314,q357,q431] [] (by decide +kernel)
def n507 := cc 7 [w19,w0,w14,w1,w22,w2,w47,w3] [q37,q103,q156,q240,q357] [] (by decide +kernel)
def n508 := cc 8 [w19,w0,w14,w1,w22,w2,w3,w4] [q4,q8,q11,q17,q26,q37,q103,q154,q223,q239,q356] [n507,n392] (by decide +kernel)
def v286 : Closed T 7 := rotateClosed n414 auto3 auto3ok
def n509 := cc 8 [w19,w0,w14,w1,w2,w47,w3,w5] [q0,q10,q26,q92,q155,q220,q235,q340,q345,q422] [v286,n507] (by decide +kernel)
def v287 : Closed T 8 := rotateClosed n420 auto3 auto3ok
def v288 : Closed T 8 := rotateClosed n506 auto3 auto3ok
def v289 : Closed T 8 := rotateClosed n505 auto3 auto3ok
def n510 := cc 9 [w19,w0,w14,w1,w2,w3,w4,w5] [q0,q8,q11,q26,q92,q154,q214,q235,q355,q420] [v287,v288,v289,n462,n508,n503,n509,n403,n501] (by decide +kernel)
def n511 := cc 8 [w0,w272,w1,w2,w3,w4,w5] [q8,q11,q86,q122,q203,q244,q351] [] (by decide +kernel)
def n512 := cc 7 [w0,w1,w274,w2,w3,w4,w5] [q8,q11,q19,q95,q228] [] (by decide +kernel)
def n513 := cc 8 [w19,w0,w273,w1,w2,w3,w4,w5] [q8,q11,q87,q93,q205,q408] [n512] (by decide +kernel)
def n514 := cc 8 [w15,w19,w0,w72,w1,w2,w3,w4] [q8,q12,q30,q84,q99,q121,q214,q238,q339,q367] [n393] (by decide +kernel)
def v290 : Closed T 8 := rotateClosed n421 auto2 auto2ok
def n515 := cc 9 [w15,w19,w0,w1,w2,w3,w4,w5] [q0,q11,q84,q92,q203,q235,q355,q420] [v290,n514,n404,n513,n511] (by decide +kernel)
def v291 : Closed T 7 := rotateClosed n186 auto2 auto2ok
def n516 := cc 8 [w41,w19,w0,w1,w2,w3,w4] [q15,q17,q19,q176,q337,q422] [v291] (by decide +kernel)
def n517 := cc 8 [w275,w19,w0,w1,w2,w3,w4] [q16,q17,q41,q103,q203,q239,q422,q423] [] (by decide +kernel)
def v292 : Closed T 8 := rotateClosed n181 auto2 auto2ok
def v293 : Closed T 8 := rotateClosed n188 auto3 auto3ok
def v294 : Closed T 8 := rotateClosed n153 auto2 auto2ok
def v295 : Closed T 8 := rotateClosed n516 auto1 auto1ok
def v296 : Closed T 8 := rotateClosed n517 auto1 auto1ok
def v297 : Closed T 8 := rotateClosed n58 auto3 auto3ok
def v298 : Closed T 8 := rotateClosed n508 auto1 auto1ok
def v299 : Closed T 8 := rotateClosed n509 auto2 auto2ok
def n518 := cc 9 [w19,w0,w72,w1,w2,w3,w4] [q0,q8,q19,q99,q134,q295,q355] [v292,v293,v294,v295,n514,v296,v297,v298,v299,v238,v239] (by decide +kernel)
def n519 := cc 5 [w0,w277,w3,w278,w4,w5] [q327,q375] [] (by decide +kernel)
def n520 := cc 5 [w0,w1,w280,w3,w259,w254] [q326] [] (by decide +kernel)
def v300 : Closed T 5 := rotateClosed n519 auto1 auto1ok
def n521 := cc 6 [w0,w1,w280,w3,w259,w4,w5] [q8] [n520,v300] (by decide +kernel)
def n522 := cc 5 [w281,w0,w2,w3,w259,w254] [] [] (by decide +kernel)
def n523 := cc 6 [w281,w0,w2,w3,w259,w4,w5] [] [n522] (by decide +kernel)
def n524 := cc 5 [w282,w0,w1,w3,w4,w5] [q13] [] (by decide +kernel)
def n525 := cc 4 [w0,w279,w284,w3,w254] [q375] [] (by decide +kernel)
def n526 := cc 5 [w0,w279,w284,w3,w4,w5] [q375] [n525] (by decide +kernel)
def n527 := cc 5 [w0,w279,w2,w3,w283,w254] [q326] [n525] (by decide +kernel)
def v301 : Closed T 5 := rotateClosed n524 auto1 auto1ok
def n528 := cc 6 [w0,w279,w2,w3,w283,w4,w5] [] [v301,n526,n527,v300] (by decide +kernel)
def v302 : Closed T 5 := rotateClosed n522 auto1 auto1ok
def n529 := cc 6 [w0,w279,w1,w2,w3,w259,w254] [q78,q127,q164] [v302,n527,n520] (by decide +kernel)
def v303 : Closed T 6 := rotateClosed n523 auto1 auto1ok
def n530 := cc 7 [w0,w279,w1,w2,w3,w259,w4,w5] [q8,q61,q79,q83,q127,q164] [v303,n529,n528,n521] (by decide +kernel)
def v304 : Closed T 4 := rotateClosed n525 auto1 auto1ok
def n531 := cc 5 [w0,w285,w2,w3,w259,w254] [] [v304] (by decide +kernel)
def v305 : Closed T 5 := rotateClosed n526 auto1 auto1ok
def n532 := cc 6 [w0,w285,w2,w3,w259,w4,w5] [q352] [v305,n531] (by decide +kernel)
def n533 := cc 5 [w286,w0,w1,w3,w259,w254] [] [] (by decide +kernel)
def n534 := cc 6 [w286,w0,w1,w3,w259,w4,w5] [] [n533] (by decide +kernel)
def v306 : Closed T 5 := rotateClosed n531 auto1 auto1ok
def n535 := cc 6 [w0,w1,w2,w3,w259,w283,w254] [q43,q114,q188] [n533,n527,v306] (by decide +kernel)
def v307 : Closed T 6 := rotateClosed n532 auto1 auto1ok
def n536 := cc 7 [w0,w1,w2,w3,w259,w283,w4,w5] [q59,q70,q114,q164,q351] [n534,n528,v307,n535] (by decide +kernel)
def n537 := cc 5 [w287,w288,w0,w2,w3,w254] [q6] [] (by decide +kernel)
def n538 := cc 6 [w287,w288,w0,w2,w3,w4,w5] [] [n537,v301] (by decide +kernel)
def n539 := cc 6 [w287,w0,w1,w2,w3,w259,w254] [] [n537] (by decide +kernel)
def n540 := cc 7 [w287,w0,w1,w2,w3,w259,w4,w5] [q8,q53] [n538,n539] (by decide +kernel)
def v308 : Closed T 5 := rotateClosed n537 auto1 auto1ok
def n541 := cc 6 [w289,w0,w1,w2,w3,w259,w254] [] [v308] (by decide +kernel)
def v309 : Closed T 6 := rotateClosed n538 auto1 auto1ok
def n542 := cc 7 [w289,w0,w1,w2,w3,w259,w4,w5] [q60,q352] [v309,n541] (by decide +kernel)
def v310 : Closed T 7 := rotateClosed n540 auto1 auto1ok
def v311 : Closed T 7 := rotateClosed n496 auto1 auto1ok
def v312 : Closed T 7 := rotateClosed n542 auto1 auto1ok
def v313 : Closed T 7 := rotateClosed n530 auto1 auto1ok
def v314 : Closed T 7 := rotateClosed n536 auto1 auto1ok
def n543 := cc 8 [w0,w1,w2,w3,w259,w4,w5] [q8,q17,q59,q114,q164,q165,q351,q352] [n540,v310,n496,v311,n542,v312,n473,n530,v313,n486,n536,v314] (by decide +kernel)
def v315 : Closed T 7 := rotateClosed n497 auto1 auto1ok
def n544 := cc 8 [w19,w0,w1,w2,w47,w3,w254] [q42,q92,q164,q165,q235,q328,q357] [n497,v315,n474,n487] (by decide +kernel)
def v316 : Closed T 8 := rotateClosed n415 auto1 auto1ok
def v317 : Closed T 8 := rotateClosed n415 auto2 auto2ok
def v318 : Closed T 8 := rotateClosed n415 auto3 auto3ok
def v319 : Closed T 8 := rotateClosed n498 auto1 auto1ok
def v320 : Closed T 8 := rotateClosed n509 auto1 auto1ok
def v321 : Closed T 8 := rotateClosed n509 auto3 auto3ok
def n545 := cc 9 [w19,w0,w1,w2,w47,w3,w4,w5] [q0,q11,q19,q92,q164,q208,q219,q235,q355,q420] [n415,v316,v317,v318,n498,v319,n475,n509,v320,v299,v321,n488,n544,n543] (by decide +kernel)
def v322 : Closed T 8 := rotateClosed n499 auto1 auto1ok
def n546 := cc 9 [w19,w0,w1,w2,w3,w254,w4] [q42,q92,q134,q235,q328,q355] [n499,v322,n476,n489,n544] (by decide +kernel)
def v323 : Closed T 9 := rotateClosed n193 auto2 auto2ok
def v324 : Closed T 9 := rotateClosed n193 auto3 auto3ok
def v325 : Closed T 9 := rotateClosed n422 auto2 auto2ok
def v326 : Closed T 9 := rotateClosed n422 auto3 auto3ok
def v327 : Closed T 9 := rotateClosed n429 auto2 auto2ok
def v328 : Closed T 9 := rotateClosed n162 auto2 auto2ok
def v329 : Closed T 9 := rotateClosed n162 auto3 auto3ok
def v330 : Closed T 9 := rotateClosed n500 auto1 auto1ok
def v331 : Closed T 9 := rotateClosed n515 auto1 auto1ok
def v332 : Closed T 9 := rotateClosed n71 auto2 auto2ok
def v333 : Closed T 9 := rotateClosed n71 auto3 auto3ok
def v334 : Closed T 9 := rotateClosed n510 auto1 auto1ok
def v335 : Closed T 9 := rotateClosed n518 auto1 auto1ok
def v336 : Closed T 9 := rotateClosed n405 auto1 auto1ok
def n547 := cc 10 [w19,w0,w1,w2,w3,w4,w5] [q19,q92,q134,q228,q295] [v323,v324,v325,v326,v327,v328,v329,n500,v330,n515,v331,v332,v333,n477,n510,v334,n518,v335,n490,n545,n546,n437,n405,v336] (by decide +kernel)
def n548 := cc 7 [w0,w291,w1,w2,w3,w4] [q4,q25,q98,q136,q385] [] (by decide +kernel)
def v337 : Closed T 7 := rotateClosed n548 auto2 auto2ok
def n549 := cc 8 [w159,w0,w1,w2,w3,w292,w5] [q17,q24,q207,q302,q420] [v337] (by decide +kernel)
def v338 : Closed T 7 := rotateClosed n430 auto2 auto2ok
def n550 := cc 8 [w0,w293,w1,w2,w3,w4,w5] [q8,q72,q93,q296] [v338] (by decide +kernel)
def n551 := cc 8 [w294,w0,w1,w2,w3,w4,w5] [q72,q93,q207,q296] [] (by decide +kernel)
def v339 : Closed T 7 := rotateClosed n431 auto2 auto2ok
def n552 := cc 8 [w0,w6,w9,w3,w4,w292,w5] [q96,q207,q214,q301] [v339] (by decide +kernel)
def v340 : Closed T 8 := rotateClosed n432 auto2 auto2ok
def n553 := cc 9 [w0,w6,w1,w2,w3,w4,w292,w5] [q93,q207,q218,q296] [n549,n551,v340,n550,n552] (by decide +kernel)
def n554 := cc 8 [w0,w1,w2,w295,w3,w4,w5] [q44,q106,q207,q309,q375,q392] [] (by decide +kernel)
def v341 : Closed T 8 := rotateClosed n433 auto2 auto2ok
def n555 := cc 9 [w0,w1,w2,w9,w3,w4,w292,w5] [q44,q214,q223,q309,q392] [v341,n552,n554] (by decide +kernel)
def n556 := cc 8 [w0,w1,w296,w2,w3,w4,w5] [q20,q72,q320,q375,q392] [] (by decide +kernel)
def v342 : Closed T 8 := rotateClosed n434 auto2 auto2ok
def v343 : Closed T 8 := rotateClosed n556 auto1 auto1ok
def n557 := cc 9 [w12,w0,w1,w2,w3,w4,w292,w5] [q115,q207,q223,q314,q407] [v342,v343] (by decide +kernel)
def n558 := cc 8 [w0,w1,w2,w298,w3,w4,w5] [q17,q44,q62,q106,q309,q351] [] (by decide +kernel)
def n559 := cc 8 [w245,w0,w1,w2,w3,w4,w5] [q20,q44,q62,q115,q176,q385] [n435] (by decide +kernel)
def v344 : Closed T 8 := rotateClosed n559 auto3 auto3ok
def v345 : Closed T 8 := rotateClosed n436 auto2 auto2ok
def v346 : Closed T 8 := rotateClosed n558 auto1 auto1ok
def n560 := cc 9 [w0,w299,w1,w2,w3,w4,w5] [q8,q19,q92,q214,q295,q407] [v344,v345,n550,v346] (by decide +kernel)
def n561 := cc 8 [w0,w1,w301,w2,w3,w4,w5] [q20,q72,q123,q320,q351,q352] [] (by decide +kernel)
def n562 := cc 8 [w0,w303,w1,w2,w3,w4,w5] [q20,q93,q136,q352,q375] [] (by decide +kernel)
def v347 : Closed T 8 := rotateClosed n562 auto2 auto2ok
def n563 := cc 9 [w300,w0,w1,w2,w3,w4,w5] [q92,q218,q295,q352,q407] [v347,n561] (by decide +kernel)
def v348 : Closed T 9 := rotateClosed n557 auto1 auto1ok
def v349 : Closed T 9 := rotateClosed n563 auto1 auto1ok
def v350 : Closed T 9 := rotateClosed n437 auto2 auto2ok
def v351 : Closed T 9 := rotateClosed n560 auto1 auto1ok
def n564 := cc 10 [w0,w1,w2,w3,w4,w292,w5] [q19,q92,q295] [n557,v348,n563,v349,v350,n553,n560,v351,n555] (by decide +kernel)
def n565 := cc 8 [w0,w14,w1,w305,w2,w3,w5] [q92,q207,q328,q351] [] (by decide +kernel)
def n566 := cc 8 [w0,w308,w1,w2,w3,w4,w5] [q136,q296,q329,q352,q375] [] (by decide +kernel)
def n567 := cc 8 [w0,w1,w2,w310,w3,w4,w5] [q167,q176,q309,q333,q351] [] (by decide +kernel)
def n568 := cc 8 [w311,w0,w1,w2,w3,w4,w5] [q20,q176,q314,q334,q351,q352] [] (by decide +kernel)
def n569 := cc 8 [w313,w0,w1,w2,w3,w4,w5] [q93,q115,q276,q334,q352] [] (by decide +kernel)
def v352 : Closed T 8 := rotateClosed n569 auto3 auto3ok
def v353 : Closed T 8 := rotateClosed n566 auto1 auto1ok
def v354 : Closed T 8 := rotateClosed n565 auto2 auto2ok
def n570 := cc 9 [w0,w1,w309,w2,w3,w4,w5] [q134,q215,q295,q328,q351] [v352,n568,v353,v354,n567] (by decide +kernel)
def n571 := cc 8 [w0,w315,w1,w2,w3,w4,w5] [q8,q123,q245,q329] [] (by decide +kernel)
def n572 := cc 8 [w0,w1,w2,w317,w3,w4,w5] [q17,q62,q106,q262,q333,q351] [] (by decide +kernel)
def n573 := cc 8 [w319,w0,w1,w2,w3,w4,w5] [q44,q136,q176,q314,q334,q385] [] (by decide +kernel)
def v355 : Closed T 8 := rotateClosed n573 auto3 auto3ok
def v356 : Closed T 8 := rotateClosed n572 auto1 auto1ok
def n574 := cc 9 [w0,w314,w1,w2,w3,w4,w5] [q8,q92,q208,q228,q328] [n569,v355,n571,v356] (by decide +kernel)
def n575 := cc 8 [w0,w320,w1,w2,w3,w4,w5] [q0,q8,q17,q136,q296,q329,q385] [] (by decide +kernel)
def n576 := cc 8 [w306,w0,w321,w1,w2,w3,w4] [q4,q136,q296,q329,q355,q385] [n548] (by decide +kernel)
def n577 := cc 8 [w306,w0,w6,w9,w3,w4,w5] [q0,q215,q301,q332,q372] [] (by decide +kernel)
def v357 : Closed T 8 := rotateClosed n571 auto2 auto2ok
def n578 := cc 9 [w306,w0,w6,w1,w2,w3,w4,w5] [q136,q215,q224,q296,q329,q371] [n576,n577,v357,n575] (by decide +kernel)
def n579 := cc 8 [w0,w1,w2,w322,w3,w4,w5] [q106,q115,q208,q333] [] (by decide +kernel)
def v358 : Closed T 8 := rotateClosed n579 auto2 auto2ok
def n580 := cc 9 [w306,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q309,q333,q373,q399] [n577,v358,n567] (by decide +kernel)
def n581 := cc 8 [w323,w0,w1,w2,w3,w4,w5] [q8,q167,q176,q314,q334,q385] [] (by decide +kernel)
def v359 : Closed T 8 := rotateClosed n569 auto2 auto2ok
def n582 := cc 9 [w306,w12,w0,w1,w2,w3,w4,w5] [q11,q215,q314,q334,q374,q413] [v359,n581] (by decide +kernel)
def n583 := cc 8 [w0,w14,w1,w324,w2,w3,w5] [q92,q207,q214,q328] [] (by decide +kernel)
def n584 := cc 8 [w306,w41,w0,w1,w2,w3,w4] [q136,q176,q314,q334,q385] [] (by decide +kernel)
def v360 : Closed T 8 := rotateClosed n584 auto1 auto1ok
def v361 : Closed T 8 := rotateClosed n583 auto2 auto2ok
def n585 := cc 9 [w306,w0,w72,w1,w2,w3,w4] [q8,q134,q217,q295,q328] [v360,n576,v361,v354] (by decide +kernel)
def v362 : Closed T 9 := rotateClosed n582 auto1 auto1ok
def v363 : Closed T 9 := rotateClosed n585 auto1 auto1ok
def v364 : Closed T 9 := rotateClosed n574 auto2 auto2ok
def v365 : Closed T 9 := rotateClosed n574 auto3 auto3ok
def v366 : Closed T 9 := rotateClosed n570 auto1 auto1ok
def n586 := cc 10 [w306,w0,w1,w2,w3,w4,w5] [q134,q295,q328,q370] [n582,v362,n578,n585,v363,n580,v364,v365,n570,v366] (by decide +kernel)
def n587 := cc 8 [w325,w0,w6,w9,w3,w4,w5] [q23,q207,q249,q301,q375,q417] [] (by decide +kernel)
def n588 := cc 9 [w325,w0,w6,w1,w2,w3,w4,w5] [q20,q207,q218,q245,q296,q416,q420] [n587] (by decide +kernel)
def n589 := cc 9 [w325,w0,w1,w2,w9,w3,w4,w5] [q44,q207,q218,q262,q309,q418] [n587] (by decide +kernel)
def n590 := cc 9 [w325,w12,w0,w1,w2,w3,w4,w5] [q44,q62,q207,q276,q314,q375,q419] [] (by decide +kernel)
def v367 : Closed T 9 := rotateClosed n590 auto1 auto1ok
def n591 := cc 10 [w325,w0,w1,w2,w3,w4,w5] [q19,q228,q295,q415] [n590,v367,n588,n589] (by decide +kernel)
def n592 := cc 7 [w0,w6,w9,w327,w4,w5] [q8,q23,q141,q351] [] (by decide +kernel)
def n593 := cc 8 [w0,w6,w1,w2,w327,w4,w5] [q8,q17,q20,q136,q212] [n592] (by decide +kernel)
def n594 := cc 7 [w329,w6,w9,w3,w4,w5] [q0,q8,q141,q249] [] (by decide +kernel)
def n595 := cc 8 [w329,w6,w1,w2,w3,w4,w5] [q0,q8,q11,q136,q245] [n594] (by decide +kernel)
def n596 := cc 7 [w0,w6,w9,w3,w4,w330] [q141,q249,q385] [] (by decide +kernel)
def n597 := cc 8 [w0,w6,w1,w2,w3,w4,w330] [q8,q17,q136,q245] [n596] (by decide +kernel)
def n598 := cc 7 [w331,w0,w6,w9,w3,w4] [q8,q208,q249] [] (by decide +kernel)
def n599 := cc 8 [w331,w0,w6,w1,w2,w3,w4] [q8,q17,q245,q296,q355] [n598] (by decide +kernel)
def n600 := cc 7 [w0,w6,w9,w3,w4,w332] [q141,q301,q332,q385] [] (by decide +kernel)
def n601 := cc 8 [w0,w6,w1,w2,w3,w4,w332] [q0,q11,q136,q296,q329,q385] [n600] (by decide +kernel)
def n602 := cc 7 [w333,w0,w6,w9,w3,w5] [q8,q208,q209,q249] [] (by decide +kernel)
def n603 := cc 8 [w333,w0,w6,w1,w2,w3,w5] [q8,q17,q215,q245] [n602] (by decide +kernel)
def n604 := cc 6 [w335,w0,w9,w4,w5] [q23,q207,q249,q301] [] (by decide +kernel)
def n605 := cc 7 [w335,w0,w1,w2,w4,w5] [q17,q207,q245] [n604] (by decide +kernel)
def n606 := cc 6 [w336,w0,w334,w4,w5] [] [] (by decide +kernel)
def v368 : Closed T 6 := rotateClosed n606 auto2 auto2ok
def v369 : Closed T 6 := rotateClosed n604 auto2 auto2ok
def n607 := cc 7 [w326,w337,w9,w3,w4,w5] [q0,q23,q141] [v368,v369] (by decide +kernel)
def n608 := cc 7 [w326,w1,w256,w2,w3,w4] [q8,q17,q20,q93] [] (by decide +kernel)
def v370 : Closed T 7 := rotateClosed n605 auto2 auto2ok
def n609 := cc 8 [w326,w1,w337,w2,w3,w4,w5] [q8,q11,q20,q72,q93,q136] [v370,n608,n607] (by decide +kernel)
def n610 := cc 7 [w336,w0,w6,w3,w4,w5] [q8,q208,q249] [] (by decide +kernel)
def v371 : Closed T 7 := rotateClosed n594 auto2 auto2ok
def v372 : Closed T 7 := rotateClosed n610 auto2 auto2ok
def v373 : Closed T 7 := rotateClosed n602 auto2 auto2ok
def v374 : Closed T 7 := rotateClosed n598 auto2 auto2ok
def v375 : Closed T 7 := rotateClosed n596 auto2 auto2ok
def n611 := cc 8 [w326,w0,w6,w9,w3,w4,w5] [q0,q141,q207,q212] [v371,v372,v373,v374,n607,n600,v375,n592] (by decide +kernel)
def v376 : Closed T 8 := rotateClosed n14 auto2 auto2ok
def v377 : Closed T 8 := rotateClosed n595 auto2 auto2ok
def v378 : Closed T 8 := rotateClosed n603 auto2 auto2ok
def v379 : Closed T 8 := rotateClosed n599 auto2 auto2ok
def v380 : Closed T 8 := rotateClosed n597 auto2 auto2ok
def n612 := cc 9 [w326,w0,w6,w1,w2,w3,w4,w5] [q8,q17,q19,q136,q207,q212] [v376,v13,v377,v378,v379,n611,n609,n601,v380,n593] (by decide +kernel)
def n613 := cc 6 [w64,w338,w337,w3,w4,w5] [q0,q8,q207,q351,q377] [] (by decide +kernel)
def n614 := cc 6 [w338,w6,w256,w9,w3,w4] [q4,q8,q23,q96,q216] [] (by decide +kernel)
def n615 := cc 7 [w338,w6,w337,w9,w3,w4,w5] [q0,q8,q23,q96,q141] [n613,n614] (by decide +kernel)
def n616 := cc 7 [w64,w0,w337,w3,w4,w5] [q8,q207,q208,q380,q388] [] (by decide +kernel)
def n617 := cc 6 [w64,w0,w256,w9,w3,w4] [q4,q5,q8,q141,q381,q388] [] (by decide +kernel)
def n618 := cc 7 [w64,w0,w337,w9,w3,w4,w5] [q0,q337,q380,q388] [n613,n617] (by decide +kernel)
def n619 := cc 7 [w0,w6,w339,w9,w3,w4,w5] [q23,q141,q375] [] (by decide +kernel)
def n620 := cc 7 [w0,w6,w256,w9,w3,w4] [q8,q23,q96,q142,q216] [n617,n614] (by decide +kernel)
def n621 := cc 7 [w0,w6,w256,w9,w3,w4,w5] [q23,q96,q141,q364,q388] [] (by decide +kernel)
def n622 := cc 7 [w340,w0,w6,w9,w3,w4] [q23,q96,q385] [] (by decide +kernel)
def n623 := cc 8 [w0,w6,w337,w9,w3,w4,w5] [q8,q23,q96,q339] [n622,n618,n616,n607,n615,n619,n620,n621] (by decide +kernel)
def n624 := cc 8 [w0,w6,w1,w256,w2,w3,w4] [q8,q17,q20,q93,q136] [n608,n620,n452] (by decide +kernel)
def n625 := cc 8 [w0,w6,w1,w256,w2,w3,w4,w5] [q8,q17,q20,q93,q136,q360] [n621] (by decide +kernel)
def n626 := cc 8 [w340,w0,w6,w1,w2,w3,w4] [q8,q17,q20,q93,q136] [n622] (by decide +kernel)
def n627 := cc 9 [w0,w6,w1,w337,w2,w3,w4,w5] [q8,q17,q20,q93,q136,q206] [n626,n609,n624,n625,n623] (by decide +kernel)
def n628 := cc 7 [w341,w342,w0,w9,w4,w5] [q23,q208,q209,q249] [n604] (by decide +kernel)
def n629 := cc 8 [w341,w342,w0,w1,w2,w4,w5] [q8,q17,q245] [n628,n605] (by decide +kernel)
def v381 : Closed T 7 := rotateClosed n628 auto2 auto2ok
def n630 := cc 8 [w343,w0,w6,w9,w3,w4,w5] [q0,q141,q337] [v381] (by decide +kernel)
def v382 : Closed T 8 := rotateClosed n629 auto2 auto2ok
def n631 := cc 9 [w343,w0,w6,w1,w2,w3,w4,w5] [q17,q93,q136,q337,q338] [v382,n630] (by decide +kernel)
def n632 := cc 7 [w0,w345,w6,w3,w4,w5] [q23,q96,q215] [] (by decide +kernel)
def n633 := cc 7 [w0,w345,w6,w9,w3,w4,w5] [q0,q23,q96,q215] [] (by decide +kernel)
def n634 := cc 7 [w341,w64,w0,w9,w3,w4,w5] [q8,q207,q378,q384,q391] [] (by decide +kernel)
def v383 : Closed T 7 := rotateClosed n633 auto2 auto2ok
def v384 : Closed T 7 := rotateClosed n632 auto2 auto2ok
def n635 := cc 8 [w341,w0,w6,w9,w3,w4,w5] [q23,q212,q301] [n634,n628,v383,v384] (by decide +kernel)
def v385 : Closed T 8 := rotateClosed n168 auto2 auto2ok
def n636 := cc 9 [w341,w0,w6,w1,w2,w3,w4,w5] [q17,q20,q212,q228,q296] [n629,n635,v385,v100] (by decide +kernel)
def n637 := cc 8 [w0,w6,w9,w3,w4,w5] [q23,q141,q212,q214,q215,q217,q249,q332,q375] [] (by decide +kernel)
def n638 := cc 8 [w12,w0,w6,w9,w3,w4,w5] [q8,q23,q249,q352,q375,q385] [] (by decide +kernel)
def n639 := cc 8 [w0,w6,w1,w9,w3,w4,w5] [q8,q23,q249,q332,q351,q375] [] (by decide +kernel)
def v386 : Closed T 8 := rotateClosed n639 auto1 auto1ok
def n640 := cc 9 [w12,w0,w6,w2,w3,w4,w5] [q11,q17,q19,q207,q219,q347,q375] [n638,n7,n108,v386,n637] (by decide +kernel)
def n641 := cc 8 [w12,w0,w6,w2,w3,w4,w5] [q20,q63,q179,q279,q352,q375,q385] [n0] (by decide +kernel)
def n642 := cc 8 [w12,w0,w1,w9,w3,w4,w5] [q19,q66,q183,q281,q335,q351,q352] [n0] (by decide +kernel)
def n643 := cc 9 [w12,w0,w1,w2,w3,w4,w5] [q8,q62,q176,q212,q215,q223,q226,q276,q334,q355,q385,q420] [n641,n642,n108,n6] (by decide +kernel)
def n644 := cc 8 [w0,w6,w1,w2,w9,w3,w4,w5] [q8,q17,q23,q141,q249,q351,q352,q360,q366,q375,q426,q432] [] (by decide +kernel)
def n645 := cc 9 [w12,w0,w6,w1,w2,w3,w4,w5] [q8,q207,q212,q215,q352,q375] [n638,n644,n639] (by decide +kernel)
def n646 := cc 8 [w41,w0,w1,w2,w3,w4,w5] [q40,q44,q136,q176,q261,q334,q385] [] (by decide +kernel)
def n647 := cc 8 [w0,w257,w1,w2,w9,w3,w4,w5] [q8,q207,q214,q215,q375] [] (by decide +kernel)
def v387 : Closed T 8 := rotateClosed n576 auto2 auto2ok
def v388 : Closed T 8 := rotateClosed n646 auto2 auto2ok
def v389 : Closed T 8 := rotateClosed n646 auto3 auto3ok
def n648 := cc 9 [w0,w257,w1,w2,w3,w4,w5] [q8,q17,q19,q134,q207,q215,q224,q245,q355,q420] [v387,v388,v389,n462,n647] (by decide +kernel)
def n649 := cc 8 [w41,w0,w6,w2,w3,w4,w5] [q8,q17,q207,q355,q385] [n0] (by decide +kernel)
def n650 := cc 7 [w347,w0,w1,w2,w3,w4] [q8,q142,q296,q329,q402] [] (by decide +kernel)
def n651 := cc 7 [w0,w257,w9,w3,w348,w5] [q8,q249,q332,q375] [] (by decide +kernel)
def n652 := cc 7 [w349,w321,w1,w2,w3,w4] [q4,q136,q296,q329,q385] [] (by decide +kernel)
def v390 : Closed T 7 := rotateClosed n650 auto2 auto2ok
def v391 : Closed T 7 := rotateClosed n652 auto2 auto2ok
def n653 := cc 8 [w0,w257,w1,w2,w3,w348,w5] [q8,q17,q245,q329] [v390,v391,n651] (by decide +kernel)
def n654 := cc 8 [w0,w257,w6,w9,w3,w4,w5] [q8,q207,q212,q215,q375] [n651] (by decide +kernel)
def v392 : Closed T 8 := rotateClosed n649 auto2 auto2ok
def v393 : Closed T 8 := rotateClosed n649 auto3 auto3ok
def n655 := cc 9 [w0,w257,w6,w1,w2,w3,w4,w5] [q17,q92,q207,q212,q215,q420] [v392,v393,n654,n653] (by decide +kernel)
def n656 := cc 7 [w349,w6,w9,w3,w4,w5] [q0,q8,q141,q301,q332,q385] [] (by decide +kernel)
def n657 := cc 7 [w350,w0,w6,w9,w4,w5] [q23,q301,q375] [] (by decide +kernel)
def v394 : Closed T 7 := rotateClosed n656 auto2 auto2ok
def n658 := cc 8 [w0,w6,w9,w3,w4,w348,w5] [q96,q212,q214,q249,q332] [n657,v394,n651] (by decide +kernel)
def n659 := cc 8 [w349,w6,w1,w2,w3,w4,w5] [q0,q8,q11,q17,q136,q296,q329,q385] [n652,n656] (by decide +kernel)
def n660 := cc 8 [w350,w0,w6,w1,w2,w4,w5] [q93,q207,q218,q296] [n657] (by decide +kernel)
def v395 : Closed T 8 := rotateClosed n659 auto2 auto2ok
def n661 := cc 9 [w0,w6,w1,w2,w3,w4,w348,w5] [q93,q212,q221,q245,q329,q420] [n660,v395,n653,n658] (by decide +kernel)
def n662 := cc 8 [w0,w6,w352,w2,w3,w4,w5] [q8,q123,q245,q329,q352] [n0] (by decide +kernel)
def n663 := cc 7 [w0,w6,w9,w3,w4,w353] [q96,q141,q249,q375] [] (by decide +kernel)
def n664 := cc 8 [w0,w6,w1,w2,w3,w4,w353] [q8,q17,q136,q245] [n663] (by decide +kernel)
def n665 := cc 7 [w159,w0,w1,w2,w3,w354] [q8,q245,q329,q397] [] (by decide +kernel)
def n666 := cc 7 [w0,w6,w9,w3,w356,w5] [q8,q141,q301,q332,q385] [] (by decide +kernel)
def v396 : Closed T 7 := rotateClosed n665 auto2 auto2ok
def n667 := cc 8 [w0,w6,w1,w2,w3,w356,w5] [q8,q17,q296,q329] [v396,n666] (by decide +kernel)
def n668 := cc 8 [w355,w290,w0,w1,w2,w3,w4] [q8,q296,q329,q405] [v396,n650] (by decide +kernel)
def n669 := cc 7 [w0,w6,w357,w3,w4,w5] [q8,q249,q332,q375] [] (by decide +kernel)
def v397 : Closed T 7 := rotateClosed n669 auto2 auto2ok
def v398 : Closed T 7 := rotateClosed n663 auto2 auto2ok
def n670 := cc 8 [w355,w0,w6,w9,w3,w4,w5] [q8,q141,q217,q301,q332,q385,q405] [v397,n666,v398] (by decide +kernel)
def v399 : Closed T 8 := rotateClosed n662 auto2 auto2ok
def v400 : Closed T 8 := rotateClosed n662 auto3 auto3ok
def v401 : Closed T 8 := rotateClosed n664 auto2 auto2ok
def n671 := cc 9 [w355,w0,w6,w1,w2,w3,w4,w5] [q8,q17,q296,q329,q355] [n668,n670,v399,v400,n667,v401] (by decide +kernel)
def n672 := cc 8 [w0,w358,w1,w2,w3,w4,w5] [q90,q136,q292,q329,q352,q375] [] (by decide +kernel)
def n673 := cc 8 [w159,w0,w1,w2,w9,w3,w4,w5] [q24,q150,q214,q221,q245,q347,q432] [] (by decide +kernel)
def n674 := cc 8 [w359,w290,w0,w1,w2,w3,w4] [q8,q224,q296,q329] [] (by decide +kernel)
def n675 := cc 8 [w360,w290,w0,w1,w2,w3,w4] [q17,q98,q136,q215,q296,q329] [] (by decide +kernel)
def v402 : Closed T 8 := rotateClosed n674 auto2 auto2ok
def v403 : Closed T 8 := rotateClosed n674 auto3 auto3ok
def v404 : Closed T 8 := rotateClosed n675 auto2 auto2ok
def v405 : Closed T 8 := rotateClosed n672 auto2 auto2ok
def v406 : Closed T 8 := rotateClosed n672 auto3 auto3ok
def n676 := cc 9 [w159,w0,w1,w2,w3,w4,w5] [q19,q134,q245,q293,q338,q341,q347,q350,q355,q420] [v402,v403,v404,n463,n673,n290,n549,v405,v406] (by decide +kernel)
def n677 := cc 7 [w159,w0,w6,w36,w9,w3,w5] [q214,q338,q347,q375,q428] [] (by decide +kernel)
def n678 := cc 8 [w159,w0,w6,w9,w3,w4,w5] [q207,q214,q249,q338,q347,q375] [n677] (by decide +kernel)
def v407 : Closed T 8 := rotateClosed n668 auto2 auto2ok
def n679 := cc 9 [w159,w0,w6,w1,w2,w3,w4,w5] [q207,q221,q245,q293,q338,q347,q420] [v407,n678] (by decide +kernel)
def n680 := cc 7 [w361,w0,w6,w9,w3,w4,w5] [q96,q141,q249,q301,q364,q387] [] (by decide +kernel)
def n681 := cc 7 [w64,w338,w0,w6,w3,w4,w5] [q0,q8,q207,q208,q376,q386] [n613] (by decide +kernel)
def n682 := cc 7 [w338,w0,w6,w222,w3,w4,w5] [q23,q144,q265] [] (by decide +kernel)
def n683 := cc 7 [w338,w0,w6,w36,w3,w4,w5] [q145,q208,q338] [] (by decide +kernel)
def v408 : Closed T 7 := rotateClosed n375 auto2 auto2ok
def v409 : Closed T 7 := rotateClosed n680 auto2 auto2ok
def n684 := cc 8 [w338,w0,w6,w9,w3,w4,w5] [q0,q23,q141,q208,q338] [v408,v409,n681,n682,n683,n615,n619] (by decide +kernel)
def n685 := cc 7 [w64,w0,w362,w3,w4,w5] [q1,q351,q380,q388] [] (by decide +kernel)
def n686 := cc 7 [w363,w0,w9,w3,w4,w5] [q8,q23,q96,q351] [] (by decide +kernel)
def n687 := cc 7 [w365,w6,w9,w3,w4,w5] [q2,q23,q141,q207,q351] [] (by decide +kernel)
def n688 := cc 7 [w366,w0,w6,w9,w4,w5] [q8,q23,q96,q301,q351] [] (by decide +kernel)
def n689 := cc 7 [w0,w6,w9,w367,w3,w5] [q1,q8,q23,q96,q351] [] (by decide +kernel)
def n690 := cc 7 [w368,w0,w6,w9,w3,w4] [q23,q332,q385] [] (by decide +kernel)
def n691 := cc 7 [w0,w6,w9,w369,w3,w4] [q8,q23,q96,q351] [] (by decide +kernel)
def n692 := cc 7 [w370,w0,w6,w9,w3,w4] [q23,q96,q385] [] (by decide +kernel)
def v410 : Closed T 7 := rotateClosed n690 auto2 auto2ok
def v411 : Closed T 7 := rotateClosed n687 auto2 auto2ok
def n693 := cc 8 [w0,w6,w9,w362,w3,w4,w5] [q8,q23,q96,q217] [n692,v410,n688,n685,n686,v411,n689,n691] (by decide +kernel)
def n694 := cc 7 [w0,w372,w9,w3,w4,w5] [q9,q141,q208,q214,q380] [] (by decide +kernel)
def n695 := cc 7 [w0,w6,w372,w9,w3,w4,w5] [q8,q141,q208,q214,q380] [] (by decide +kernel)
def n696 := cc 7 [w373,w374,w0,w6,w4,w5] [] [] (by decide +kernel)
def n697 := cc 7 [w371,w64,w0,w6,w3,w4,w5] [q8,q208,q380,q383,q390] [] (by decide +kernel)
def v412 : Closed T 7 := rotateClosed n696 auto2 auto2ok
def n698 := cc 8 [w371,w0,w6,w9,w3,w4,w5] [q141,q208,q214] [v412,n697,n695,n694] (by decide +kernel)
def n699 := cc 8 [w373,w0,w6,w9,w3,w4,w5] [q23,q207,q208,q301] [] (by decide +kernel)
def n700 := cc 7 [w341,w64,w0,w3,w4,w5] [] [] (by decide +kernel)
def n701 := cc 7 [w64,w326,w0,w3,w4,w5] [] [] (by decide +kernel)
def n702 := cc 7 [w343,w64,w0,w3,w4,w5] [] [] (by decide +kernel)
def v413 : Closed T 7 := rotateClosed n700 auto2 auto2ok
def v414 : Closed T 7 := rotateClosed n702 auto2 auto2ok
def v415 : Closed T 7 := rotateClosed n701 auto2 auto2ok
def n703 := cc 8 [w64,w0,w6,w3,w4,w5] [q337,q375,q385] [v413,v414,v415,n616,n0] (by decide +kernel)
def n704 := cc 7 [w373,w64,w0,w3,w4,w5] [] [] (by decide +kernel)
def n705 := cc 7 [w64,w338,w0,w3,w4,w5] [] [] (by decide +kernel)
def n706 := cc 7 [w371,w64,w0,w3,w4,w5] [] [] (by decide +kernel)
def v416 : Closed T 7 := rotateClosed n704 auto2 auto2ok
def v417 : Closed T 7 := rotateClosed n706 auto2 auto2ok
def v418 : Closed T 7 := rotateClosed n705 auto2 auto2ok
def n707 := cc 8 [w64,w0,w9,w3,w4,w5] [q0,q208,q375,q385] [v416,v417,v418,n209,n685,n0] (by decide +kernel)
def v419 : Closed T 7 := rotateClosed n634 auto2 auto2ok
def v420 : Closed T 7 := rotateClosed n697 auto2 auto2ok
def v421 : Closed T 7 := rotateClosed n681 auto2 auto2ok
def v422 : Closed T 7 := rotateClosed n618 auto2 auto2ok
def n708 := cc 8 [w64,w0,w6,w9,w3,w4,w5] [q0,q8,q207,q208,q375,q385] [n634,v419,n697,v420,n681,v421,n618,v422] (by decide +kernel)
def n709 := cc 7 [w0,w6,w375,w9,w3,w4,w5] [q23,q141,q249,q332,q364,q379,q428] [] (by decide +kernel)
def n710 := cc 7 [w0,w6,w36,w3,w376,w5] [q3,q249,q332,q428] [] (by decide +kernel)
def n711 := cc 6 [w0,w6,w36,w198,w3,w254] [q145,q251,q332,q365,q429] [] (by decide +kernel)
def n712 := cc 7 [w0,w6,w36,w198,w3,w4,w5] [q0,q208,q214,q217,q347] [n711] (by decide +kernel)
def n713 := cc 7 [w0,w6,w36,w9,w3,w254,w5] [q145,q216,q249,q332,q375] [n711] (by decide +kernel)
def n714 := cc 8 [w0,w6,w36,w9,w3,w4,w5] [q0,q96,q345,q347,q375] [n677,n683,n709,n712,n713,n710] (by decide +kernel)
def n715 := cc 7 [w377,w6,w9,w3,w4,w5] [q3,q96,q141,q249,q351,q375] [] (by decide +kernel)
def n716 := cc 7 [w379,w0,w6,w9,w4,w5] [q23,q332,q385] [] (by decide +kernel)
def n717 := cc 7 [w380,w0,w9,w3,w4,w5] [q3,q96,q249,q332,q351,q375] [] (by decide +kernel)
def n718 := cc 7 [w381,w6,w9,w3,w4,w5] [q141,q301,q332,q351,q385] [] (by decide +kernel)
def n719 := cc 7 [w382,w0,w6,w9,w4,w5] [q23,q301,q375] [] (by decide +kernel)
def n720 := cc 7 [w0,w6,w9,w3,w383,w5] [q141,q210,q332,q385] [] (by decide +kernel)
def n721 := cc 7 [w384,w0,w6,w9,w3,w4] [q96,q141,q249,q375] [] (by decide +kernel)
def v423 : Closed T 7 := rotateClosed n716 auto2 auto2ok
def v424 : Closed T 7 := rotateClosed n718 auto2 auto2ok
def v425 : Closed T 7 := rotateClosed n720 auto2 auto2ok
def n722 := cc 8 [w0,w6,w9,w3,w4,w376,w5] [q96,q212,q249,q332,q351] [n721,n719,v423,n717,n715,v424,n710,v425] (by decide +kernel)
def n723 := cc 7 [w385,w386,w0,w6,w3,w4] [q210,q301,q332,q385,q404] [] (by decide +kernel)
def n724 := cc 8 [w385,w0,w6,w9,w3,w4,w5] [q141,q215,q217,q301,q332,q385] [n723] (by decide +kernel)
def v426 : Closed T 7 := rotateClosed n723 auto2 auto2ok
def n725 := cc 8 [w387,w0,w6,w9,w3,w4,w5] [q0,q208,q214,q217,q375] [v426] (by decide +kernel)
def n726 := cc 7 [w0,w6,w9,w3,w254,w388] [q143,q249,q332,q375] [] (by decide +kernel)
def v427 : Closed T 7 := rotateClosed n469 auto2 auto2ok
def v428 : Closed T 7 := rotateClosed n713 auto2 auto2ok
def n727 := cc 8 [w0,w6,w9,w3,w254,w4,w5] [q96,q141,q249,q301,q347,q351,q375] [n469,v427,n709,n713,v428,n726] (by decide +kernel)
def n728 := cc 7 [w0,w6,w389,w3,w4,w5] [q96,q141,q143,q249,q375] [] (by decide +kernel)
def n729 := cc 7 [w390,w0,w6,w3,w4,w5] [q96,q141,q249,q375] [] (by decide +kernel)
def n730 := cc 8 [w0,w6,w9,w3,w4,w5,w388] [q96,q141,q212,q214,q249] [n729,n728,n726] (by decide +kernel)
def n731 := cc 8 [w360,w0,w6,w9,w3,w4,w5] [q23,q141,q215,q217,q249,q332,q442] [] (by decide +kernel)
def v429 : Closed T 8 := rotateClosed n577 auto2 auto2ok
def v430 : Closed T 8 := rotateClosed n670 auto2 auto2ok
def v431 : Closed T 8 := rotateClosed n724 auto2 auto2ok
def v432 : Closed T 8 := rotateClosed n345 auto2 auto2ok
def v433 : Closed T 8 := rotateClosed n731 auto2 auto2ok
def v434 : Closed T 8 := rotateClosed n268 auto2 auto2ok
def v435 : Closed T 8 := rotateClosed n635 auto2 auto2ok
def v436 : Closed T 8 := rotateClosed n699 auto2 auto2ok
def v437 : Closed T 8 := rotateClosed n587 auto2 auto2ok
def v438 : Closed T 8 := rotateClosed n376 auto2 auto2ok
def v439 : Closed T 8 := rotateClosed n698 auto2 auto2ok
def v440 : Closed T 8 := rotateClosed n725 auto2 auto2ok
def v441 : Closed T 8 := rotateClosed n630 auto2 auto2ok
def v442 : Closed T 8 := rotateClosed n678 auto2 auto2ok
def v443 : Closed T 8 := rotateClosed n611 auto2 auto2ok
def v444 : Closed T 8 := rotateClosed n684 auto2 auto2ok
def v445 : Closed T 8 := rotateClosed n284 auto2 auto2ok
def v446 : Closed T 8 := rotateClosed n470 auto2 auto2ok
def v447 : Closed T 8 := rotateClosed n654 auto2 auto2ok
def v448 : Closed T 8 := rotateClosed n623 auto2 auto2ok
def v449 : Closed T 8 := rotateClosed n714 auto2 auto2ok
def v450 : Closed T 8 := rotateClosed n693 auto2 auto2ok
def v451 : Closed T 8 := rotateClosed n297 auto2 auto2ok
def v452 : Closed T 8 := rotateClosed n658 auto2 auto2ok
def v453 : Closed T 8 := rotateClosed n722 auto2 auto2ok
def v454 : Closed T 8 := rotateClosed n552 auto2 auto2ok
def n732 := cc 9 [w0,w6,w9,w3,w4,w5] [] [n577,v429,n670,v430,n724,v431,n345,v432,n731,v433,n268,v434,n635,v435,n699,v436,n587,v437,n376,v438,n698,v439,n725,v440,n630,v441,n708,n703,n707,n678,v442,n611,v443,n684,v444,n202,n284,v445,n470,v446,n654,v447,n623,v448,n714,v449,n693,v450,n213,n727,n297,v451,n658,v452,n722,v453,n552,v454,n730] (by decide +kernel)
def n733 := cc 7 [w94,w64,w0,w3,w4,w5] [] [] (by decide +kernel)
def n734 := cc 7 [w64,w7,w0,w3,w4,w5] [] [] (by decide +kernel)
def n735 := cc 7 [w18,w64,w0,w3,w4,w5] [] [] (by decide +kernel)
def v455 : Closed T 7 := rotateClosed n733 auto2 auto2ok
def v456 : Closed T 7 := rotateClosed n735 auto3 auto3ok
def v457 : Closed T 7 := rotateClosed n734 auto2 auto2ok
def n736 := cc 8 [w64,w0,w1,w3,w4,w5] [q0,q8,q375,q385] [v455,v456,v457,n74] (by decide +kernel)
def n737 := cc 8 [w64,w0,w6,w1,w3,w4,w5] [q8,q207,q375,q385] [n0] (by decide +kernel)
def n738 := cc 8 [w64,w0,w1,w9,w3,w4,w5] [q0,q208,q375,q385] [n0] (by decide +kernel)
def n739 := cc 8 [w64,w0,w6,w1,w9,w3,w4,w5] [q0,q207,q375,q385] [] (by decide +kernel)
def n740 := cc 8 [w0,w6,w14,w9,w3,w4,w5] [q8,q207,q214,q375] [] (by decide +kernel)
def n741 := cc 7 [w392,w6,w9,w3,w4,w5] [q141,q301,q332,q351,q385] [] (by decide +kernel)
def n742 := cc 7 [w394,w0,w6,w9,w4,w5] [q23,q301,q375] [] (by decide +kernel)
def v458 : Closed T 7 := rotateClosed n741 auto2 auto2ok
def n743 := cc 8 [w0,w6,w9,w3,w4,w393,w5] [q96,q212,q249,q332,q351] [n742,v458] (by decide +kernel)
def n744 := cc 8 [w359,w0,w6,w9,w3,w4,w5] [q8,q217,q301,q332,q385] [] (by decide +kernel)
def n745 := cc 8 [w15,w0,w6,w9,w3,w4,w5] [q11,q218,q221,q249,q375] [] (by decide +kernel)
def v459 : Closed T 8 := rotateClosed n744 auto2 auto2ok
def v460 : Closed T 8 := rotateClosed n175 auto2 auto2ok
def v461 : Closed T 8 := rotateClosed n145 auto1 auto1ok
def v462 : Closed T 8 := rotateClosed n145 auto3 auto3ok
def v463 : Closed T 8 := rotateClosed n641 auto1 auto1ok
def v464 : Closed T 8 := rotateClosed n638 auto1 auto1ok
def v465 : Closed T 8 := rotateClosed n745 auto1 auto1ok
def v466 : Closed T 8 := rotateClosed n745 auto3 auto3ok
def v467 : Closed T 8 := rotateClosed n36 auto2 auto2ok
def v468 : Closed T 8 := rotateClosed n740 auto2 auto2ok
def v469 : Closed T 8 := rotateClosed n77 auto2 auto2ok
def v470 : Closed T 8 := rotateClosed n743 auto2 auto2ok
def n746 := cc 9 [w0,w6,w1,w9,w3,w4,w5] [q0,q8,q207,q208,q214,q217,q347] [n744,v459,n175,v460,v461,v462,v463,n638,v464,n642,v465,v466,n739,n737,n738,n736,n36,v467,n740,v468,n77,v469,n743,v470] (by decide +kernel)
def n747 := cc 8 [w64,w0,w1,w2,w3,w4,w5] [q0,q8,q11,q17,q207,q208,q218,q219,q375,q385] [] (by decide +kernel)
def n748 := cc 8 [w64,w0,w6,w1,w2,w3,w4,w5] [q8,q207,q352,q375,q385] [] (by decide +kernel)
def n749 := cc 8 [w64,w0,w1,w2,w9,w3,w4,w5] [q0,q20,q208,q352,q375,q385] [] (by decide +kernel)
def n750 := cc 8 [w64,w0,w6,w1,w2,w9,w3,w4,w5] [q375] [] (by decide +kernel)
def n751 := cc 8 [w0,w6,w14,w2,w9,w3,w4,w5] [q8,q207,q214,q215,q375] [] (by decide +kernel)
def n752 := cc 8 [w15,w0,w6,w1,w9,w3,w4,w5] [q11,q212,q214,q221,q226,q375] [] (by decide +kernel)
def n753 := cc 8 [w0,w6,w1,w2,w36,w3,w4,w5] [q0,q11,q47,q223,q262,q347,q426] [] (by decide +kernel)
def n754 := cc 8 [w387,w0,w6,w1,w2,w3,w4,w5] [q0,q212,q217,q375,q395] [] (by decide +kernel)
def v471 : Closed T 8 := rotateClosed n754 auto2 auto2ok
def v472 : Closed T 8 := rotateClosed n752 auto1 auto1ok
def v473 : Closed T 8 := rotateClosed n752 auto2 auto2ok
def v474 : Closed T 8 := rotateClosed n752 auto3 auto3ok
def v475 : Closed T 8 := rotateClosed n673 auto2 auto2ok
def v476 : Closed T 8 := rotateClosed n647 auto2 auto2ok
def v477 : Closed T 8 := rotateClosed n751 auto1 auto1ok
def v478 : Closed T 8 := rotateClosed n751 auto2 auto2ok
def v479 : Closed T 8 := rotateClosed n751 auto3 auto3ok
def v480 : Closed T 8 := rotateClosed n753 auto2 auto2ok
def n755 := cc 9 [w0,w6,w1,w2,w9,w3,w4,w5] [q0,q8,q11,q17,q44,q136,q207,q208,q214,q217,q218,q219,q221,q224,q245,q347] [n754,v471,n638,v464,n752,v472,v473,v474,n750,n748,n749,n747,n673,v475,n647,v476,n751,v477,v478,v479,n753,v480] (by decide +kernel)
def n756 := cc 8 [w0,w6,w1,w270,w3,w4,w5] [q8,q207,q214] [n0] (by decide +kernel)
def n757 := cc 8 [w0,w6,w1,w2,w46,w3,w4,w5] [q0,q208,q212,q217,q375] [] (by decide +kernel)
def n758 := cc 8 [w0,w6,w14,w2,w3,w393,w5] [q8,q123,q245,q329,q395] [] (by decide +kernel)
def v481 : Closed T 8 := rotateClosed n757 auto1 auto1ok
def n759 := cc 9 [w0,w6,w14,w1,w2,w3,w4,w5] [q8,q17,q92,q207,q212,q214,q215,q420] [v393,n751,n758,n740,v481,n756] (by decide +kernel)
def n760 := cc 8 [w395,w0,w1,w2,w3,w4,w5] [q8,q93,q245,q329,q351] [] (by decide +kernel)
def n761 := cc 8 [w392,w6,w1,w2,w3,w4,w5] [q8,q11,q136,q296,q329,q351,q385] [n741] (by decide +kernel)
def n762 := cc 8 [w394,w0,w6,w1,w2,w4,w5] [q62,q93,q218,q296,q351] [n742] (by decide +kernel)
def v482 : Closed T 8 := rotateClosed n761 auto2 auto2ok
def n763 := cc 9 [w0,w6,w1,w2,w3,w4,w393,w5] [q93,q212,q221,q245,q329] [n762,n760,v482,n758,n743] (by decide +kernel)
def n764 := cc 8 [w0,w6,w1,w396,w3,w4,w5] [q136,q296,q329,q351,q352,q375] [n0] (by decide +kernel)
def n765 := cc 9 [w359,w0,w6,w1,w2,w3,w4,w5] [q8,q224,q296,q329,q355,q400] [n674,n744,v400,n764,n672] (by decide +kernel)
def n766 := cc 8 [w0,w1,w397,w2,w3,w4,w5] [q17,q123,q336,q375,q392] [] (by decide +kernel)
def n767 := cc 9 [w15,w0,w6,w1,w2,w3,w4,w5] [q8,q11,q84,q218,q245,q341,q350,q409] [n754,n752,n745,n766] (by decide +kernel)
def n768 := cc 8 [w0,w6,w1,w2,w3,w254,w388] [q137,q212,q221,q245,q329] [n726] (by decide +kernel)
def v483 : Closed T 8 := rotateClosed n476 auto2 auto2ok
def n769 := cc 9 [w0,w6,w1,w2,w3,w254,w4,w5] [q93,q136,q245,q296,q328,q347,q350,q355,q420] [n476,v483,n768,n727] (by decide +kernel)
def n770 := cc 8 [w0,w398,w1,w2,w3,w4,w5] [q8,q123,q136,q245] [] (by decide +kernel)
def n771 := cc 8 [w399,w0,w1,w2,w3,w4,w5] [q123,q136,q137,q212,q245] [] (by decide +kernel)
def n772 := cc 7 [w0,w6,w401,w3,w4,w5] [q96,q141,q249,q375] [] (by decide +kernel)
def v484 : Closed T 7 := rotateClosed n772 auto1 auto1ok
def n773 := cc 8 [w0,w6,w402,w2,w3,w4,w5] [q8,q123,q136,q245,q352] [v484] (by decide +kernel)
def n774 := cc 8 [w403,w0,w6,w1,w3,w4,w5] [q93,q136,q245,q351,q352,q375] [n729] (by decide +kernel)
def v485 : Closed T 8 := rotateClosed n774 auto1 auto1ok
def v486 : Closed T 8 := rotateClosed n773 auto1 auto1ok
def n775 := cc 9 [w0,w6,w1,w2,w3,w4,w5,w388] [q136,q212,q221,q245] [n774,v485,n771,n770,n773,v486,n768,n730] (by decide +kernel)
def n776 := cc 8 [w0,w404,w1,w2,w3,w4,w5] [q136,q192,q215,q252,q296,q329] [] (by decide +kernel)
def n777 := cc 8 [w0,w406,w1,w2,w3,w4,w5] [q8,q123,q245,q329] [] (by decide +kernel)
def v487 : Closed T 8 := rotateClosed n777 auto2 auto2ok
def n778 := cc 9 [w360,w0,w6,w1,w2,w3,w4,w5] [q136,q215,q224,q245,q296,q329,q441] [n675,n731,v487,n776] (by decide +kernel)
def v488 : Closed T 9 := rotateClosed n578 auto2 auto2ok
def v489 : Closed T 9 := rotateClosed n671 auto2 auto2ok
def v490 : Closed T 9 := rotateClosed n765 auto1 auto1ok
def v491 : Closed T 9 := rotateClosed n765 auto2 auto2ok
def v492 : Closed T 9 := rotateClosed n765 auto3 auto3ok
def v493 : Closed T 9 := rotateClosed n346 auto2 auto2ok
def v494 : Closed T 9 := rotateClosed n778 auto2 auto2ok
def v495 : Closed T 9 := rotateClosed n269 auto2 auto2ok
def v496 : Closed T 9 := rotateClosed n636 auto2 auto2ok
def v497 : Closed T 9 := rotateClosed n176 auto1 auto1ok
def v498 : Closed T 9 := rotateClosed n176 auto2 auto2ok
def v499 : Closed T 9 := rotateClosed n176 auto3 auto3ok
def v500 : Closed T 9 := rotateClosed n588 auto2 auto2ok
def v501 : Closed T 9 := rotateClosed n377 auto2 auto2ok
def v502 : Closed T 9 := rotateClosed n146 auto1 auto1ok
def v503 : Closed T 9 := rotateClosed n146 auto2 auto2ok
def v504 : Closed T 9 := rotateClosed n146 auto3 auto3ok
def v505 : Closed T 9 := rotateClosed n645 auto1 auto1ok
def v506 : Closed T 9 := rotateClosed n640 auto1 auto1ok
def v507 : Closed T 9 := rotateClosed n643 auto1 auto1ok
def v508 : Closed T 9 := rotateClosed n767 auto1 auto1ok
def v509 : Closed T 9 := rotateClosed n767 auto2 auto2ok
def v510 : Closed T 9 := rotateClosed n767 auto3 auto3ok
def v511 : Closed T 9 := rotateClosed n631 auto2 auto2ok
def v512 : Closed T 9 := rotateClosed n679 auto2 auto2ok
def v513 : Closed T 9 := rotateClosed n676 auto2 auto2ok
def v514 : Closed T 9 := rotateClosed n612 auto2 auto2ok
def v515 : Closed T 9 := rotateClosed n37 auto1 auto1ok
def v516 : Closed T 9 := rotateClosed n37 auto2 auto2ok
def v517 : Closed T 9 := rotateClosed n37 auto3 auto3ok
def v518 : Closed T 9 := rotateClosed n285 auto2 auto2ok
def v519 : Closed T 9 := rotateClosed n477 auto2 auto2ok
def v520 : Closed T 9 := rotateClosed n655 auto2 auto2ok
def v521 : Closed T 9 := rotateClosed n648 auto2 auto2ok
def v522 : Closed T 9 := rotateClosed n759 auto1 auto1ok
def v523 : Closed T 9 := rotateClosed n759 auto2 auto2ok
def v524 : Closed T 9 := rotateClosed n759 auto3 auto3ok
def v525 : Closed T 9 := rotateClosed n627 auto2 auto2ok
def v526 : Closed T 9 := rotateClosed n81 auto1 auto1ok
def v527 : Closed T 9 := rotateClosed n81 auto2 auto2ok
def v528 : Closed T 9 := rotateClosed n81 auto3 auto3ok
def v529 : Closed T 9 := rotateClosed n303 auto2 auto2ok
def v530 : Closed T 9 := rotateClosed n661 auto2 auto2ok
def v531 : Closed T 9 := rotateClosed n763 auto1 auto1ok
def v532 : Closed T 9 := rotateClosed n763 auto2 auto2ok
def v533 : Closed T 9 := rotateClosed n763 auto3 auto3ok
def v534 : Closed T 9 := rotateClosed n553 auto2 auto2ok
def v535 : Closed T 9 := rotateClosed n746 auto1 auto1ok
def n779 := cc 10 [w0,w6,w1,w2,w3,w4,w5] [q19,q134,q228] [n578,v488,n671,v489,n765,v490,v491,v492,n346,v493,n778,v494,n269,v495,n636,v496,n176,v497,v498,v499,n588,v500,n377,v501,n146,v502,v503,v504,n645,v505,n640,v506,n643,v507,n767,v508,v509,v510,n631,v511,n679,v512,n676,v513,n612,v514,n37,v515,v516,v517,n203,n285,v518,n477,v519,n655,v520,n648,v521,n759,v522,v523,v524,n627,v525,n81,v526,v527,v528,n755,n217,n769,n303,v529,n661,v530,n763,v531,v532,v533,n553,v534,n775,n746,v535,n732] (by decide +kernel)
def n780 := cc 8 [w361,w0,w1,w2,w9,w3,w4,w5] [q51,q169,q208,q219,q262,q309,q366] [n680] (by decide +kernel)
def n781 := cc 7 [w407,w0,w1,w2,w4,w5] [q44,q262,q309,q352] [] (by decide +kernel)
def n782 := cc 7 [w338,w1,w2,w408,w4,w5] [q44,q106,q169,q352] [] (by decide +kernel)
def n783 := cc 7 [w338,w1,w2,w367,w3,w5] [q44,q106,q170,q352] [] (by decide +kernel)
def v536 : Closed T 7 := rotateClosed n781 auto2 auto2ok
def n784 := cc 8 [w338,w1,w2,w362,w3,w4,w5] [q44,q106,q167,q192,q352,q399] [v536,n782,n783] (by decide +kernel)
def n785 := cc 8 [w338,w0,w1,w2,w222,w3,w4,w5] [q0,q11,q44,q169,q264] [n682] (by decide +kernel)
def n786 := cc 8 [w338,w0,w1,w2,w36,w3,w4,w5] [q0,q11,q47,q106,q170,q208,q420] [n683] (by decide +kernel)
def v537 : Closed T 8 := rotateClosed n380 auto2 auto2ok
def v538 : Closed T 8 := rotateClosed n780 auto2 auto2ok
def n787 := cc 9 [w338,w0,w1,w2,w9,w3,w4,w5] [q0,q11,q44,q106,q167,q208] [v537,v538,n684,n785,n786,n784] (by decide +kernel)
def v539 : Closed T 7 := rotateClosed n782 auto2 auto2ok
def n788 := cc 8 [w365,w1,w2,w9,w3,w4,w5] [q44,q167,q214,q352] [v539,n687] (by decide +kernel)
def n789 := cc 8 [w366,w0,w1,w2,w9,w4,w5] [q44,q106,q309,q351,q352] [n688] (by decide +kernel)
def n790 := cc 8 [w0,w1,w2,w9,w367,w3,w5] [q44,q106,q170,q351,q352,q355] [n783,n689] (by decide +kernel)
def n791 := cc 8 [w368,w0,w1,w2,w9,w3,w4] [q44,q333,q351,q352] [n690] (by decide +kernel)
def n792 := cc 8 [w0,w1,w2,w9,w369,w3,w4] [q44,q106,q167,q351,q352,q399] [n691] (by decide +kernel)
def n793 := cc 8 [w370,w0,w1,w2,w9,w3,w4] [q44,q106,q167,q351,q352] [n692] (by decide +kernel)
def v540 : Closed T 8 := rotateClosed n791 auto2 auto2ok
def v541 : Closed T 8 := rotateClosed n84 auto1 auto1ok
def v542 : Closed T 8 := rotateClosed n788 auto2 auto2ok
def n794 := cc 9 [w0,w1,w2,w9,w362,w3,w4,w5] [q44,q106,q134,q217,q352] [n793,v540,n789,n84,v541,n784,v542,n693,n790,n792] (by decide +kernel)
def n795 := cc 8 [w373,w374,w0,w1,w2,w4,w5] [q44,q72,q262,q309,q352] [n781] (by decide +kernel)
def v543 : Closed T 8 := rotateClosed n795 auto2 auto2ok
def n796 := cc 9 [w371,w0,w1,w2,w9,w3,w4,w5] [q19,q167,q208,q214,q352] [v543,n698,n127,v72] (by decide +kernel)
def n797 := cc 9 [w373,w0,w1,w2,w9,w3,w4,w5] [q44,q62,q208,q218,q262,q293,q309,q352] [n795,n699] (by decide +kernel)
def n798 := cc 9 [w12,w0,w1,w9,w3,w4,w5] [q0,q8,q19,q207,q208,q214,q217,q347,q352,q375] [n638,n7,n639,n637,n6] (by decide +kernel)
def n799 := cc 9 [w12,w0,w1,w2,w9,w3,w4,w5] [q0,q8,q44,q176,q207,q208,q223,q226,q276,q375] [n638,n644,v386] (by decide +kernel)
def n800 := cc 8 [w409,w0,w1,w2,w3,w4,w5] [q136,q176,q314,q334,q352,q385] [] (by decide +kernel)
def n801 := cc 8 [w0,w410,w1,w2,w9,w3,w4,w5] [q8,q17,q27,q44,q214,q255,q262,q333,q336,q432] [] (by decide +kernel)
def n802 := cc 8 [w0,w14,w2,w9,w3,w393,w5] [q106,q262,q333,q351,q375,q396,q432] [] (by decide +kernel)
def n803 := cc 8 [w0,w14,w1,w22,w2,w9,w3,w4,w5] [q215,q333,q336,q366] [] (by decide +kernel)
def n804 := cc 8 [w0,w14,w1,w2,w198,w3,w4,w5] [q26,q154,q208,q214,q215,q333,q356] [] (by decide +kernel)
def v544 : Closed T 8 := rotateClosed n800 auto3 auto3ok
def n805 := cc 9 [w0,w14,w1,w2,w9,w3,w4,w5] [q0,q8,q44,q154,q207,q208,q214,q223,q228,q333] [v544,n647,n751,n740,n801,n803,n804,n802] (by decide +kernel)
def n806 := cc 8 [w0,w412,w2,w9,w3,w4,w5] [q8,q106,q123,q262,q333,q352] [n0] (by decide +kernel)
def n807 := cc 8 [w413,w0,w1,w9,w3,w4,w5] [q106,q333,q351,q352] [n0] (by decide +kernel)
def n808 := cc 8 [w0,w1,w2,w36,w3,w393,w5] [q106,q221,q262,q333,q351,q352,q392,q410] [] (by decide +kernel)
def n809 := cc 8 [w0,w1,w2,w46,w3,w4,w5] [q62,q106,q262,q333,q351,q427] [] (by decide +kernel)
def n810 := cc 8 [w392,w1,w2,w9,w3,w4,w5] [q11,q309,q333,q351,q399] [n741] (by decide +kernel)
def n811 := cc 8 [w394,w0,w1,w2,w9,w4,w5] [q44,q62,q106,q218,q309,q351] [n742] (by decide +kernel)
def v545 : Closed T 8 := rotateClosed n810 auto2 auto2ok
def v546 : Closed T 8 := rotateClosed n806 auto1 auto1ok
def n812 := cc 9 [w0,w1,w2,w9,w3,w4,w393,w5] [q106,q223,q262,q333,q351,q392] [n811,n807,v545,n743,n802,v546,n808,n809] (by decide +kernel)
def n813 := cc 8 [w0,w1,w2,w415,w3,w4,w5] [q17,q106,q262,q333,q352] [] (by decide +kernel)
def v547 : Closed T 8 := rotateClosed n813 auto3 auto3ok
def n814 := cc 9 [w359,w0,w1,w2,w9,w3,w4,w5] [q167,q217,q226,q309,q333,q401] [n744,v547] (by decide +kernel)
def n815 := cc 8 [w0,w1,w416,w9,w3,w4,w5] [q0,q281,q335,q352,q392,q432] [n0] (by decide +kernel)
def n816 := cc 8 [w0,w358,w2,w9,w3,w4,w5] [q8,q141,q212,q219,q332,q366,q375] [n0] (by decide +kernel)
def n817 := cc 8 [w0,w358,w1,w2,w9,w3,w4,w5] [q8,q207,q212,q301,q352,q366,q375] [] (by decide +kernel)
def v548 : Closed T 8 := rotateClosed n817 auto2 auto2ok
def v549 : Closed T 8 := rotateClosed n816 auto2 auto2ok
def v550 : Closed T 8 := rotateClosed n815 auto1 auto1ok
def n818 := cc 9 [w15,w0,w1,w2,w9,w3,w4,w5] [q11,q92,q214,q219,q221,q223,q226,q262,q407] [n752,n745,v548,v549,v550] (by decide +kernel)
def n819 := cc 8 [w360,w0,w1,w2,w198,w3,w4] [q167,q215,q266,q309,q333,q351,q352,q355,q385] [] (by decide +kernel)
def v551 : Closed T 8 := rotateClosed n348 auto2 auto2ok
def v552 : Closed T 8 := rotateClosed n819 auto2 auto2ok
def v553 : Closed T 8 := rotateClosed n39 auto1 auto1ok
def v554 : Closed T 8 := rotateClosed n804 auto2 auto2ok
def v555 : Closed T 8 := rotateClosed n804 auto3 auto3ok
def v556 : Closed T 8 := rotateClosed n808 auto1 auto1ok
def v557 : Closed T 8 := rotateClosed n809 auto1 auto1ok
def n820 := cc 9 [w0,w1,w2,w36,w3,w4,w5] [q19,q106,q134,q214,q223,q293,q333,q355,q392,q420] [v551,v552,n39,v553,n483,n753,v554,v555,n808,v556,n809,v557] (by decide +kernel)
def n821 := cc 8 [w0,w1,w2,w375,w9,w3,w4,w5] [q44,q109,q170,q214,q223,q266,q311,q333,q366,q432] [n709] (by decide +kernel)
def n822 := cc 7 [w377,w1,w2,w36,w3,w5] [q3,q170,q262,q351,q352] [] (by decide +kernel)
def n823 := cc 7 [w417,w0,w1,w2,w3,w4] [q210,q333,q352,q414] [] (by decide +kernel)
def n824 := cc 7 [w0,w1,w2,w36,w3,w418] [q3,q262,q333,q351,q352] [] (by decide +kernel)
def v558 : Closed T 7 := rotateClosed n823 auto2 auto2ok
def n825 := cc 8 [w0,w1,w2,w36,w3,w376,w5] [q106,q214,q333,q352,q392] [v558,n822,n710,n824] (by decide +kernel)
def n826 := cc 7 [w0,w1,w2,w36,w198,w3,w254] [q170,q214,q223,q266] [n711] (by decide +kernel)
def n827 := cc 8 [w0,w1,w2,w36,w198,w3,w4,w5] [q0,q47,q48,q208,q214,q217,q223,q333] [n712,n826] (by decide +kernel)
def n828 := cc 8 [w0,w1,w2,w36,w9,w3,w254,w5] [q7,q106,q170,q214,q223,q262,q311,q333,q432] [n713,n826] (by decide +kernel)
def n829 := cc 9 [w0,w1,w2,w36,w9,w3,w4,w5] [q0,q44,q106,q208,q214,q223,q293,q333,q392,q432] [n786,n714,n821,n827,n828,n825] (by decide +kernel)
def n830 := cc 8 [w377,w1,w2,w9,w3,w4,w5] [q106,q167,q262,q351,q352] [n715,n822] (by decide +kernel)
def n831 := cc 8 [w379,w0,w1,w2,w9,w4,w5] [q44,q333,q351,q352] [n716] (by decide +kernel)
def n832 := cc 8 [w381,w1,w2,w9,w3,w4,w5] [q167,q309,q333,q351,q352,q399] [n718] (by decide +kernel)
def n833 := cc 8 [w382,w0,w1,w2,w9,w4,w5] [q44,q106,q309,q351,q352] [n719] (by decide +kernel)
def v559 : Closed T 7 := rotateClosed n824 auto2 auto2ok
def n834 := cc 8 [w0,w1,w2,w9,w3,w383,w5] [q167,q309,q333,q351,q352] [n720,v559] (by decide +kernel)
def n835 := cc 8 [w384,w0,w1,w2,w9,w3,w4] [q106,q167,q262,q351,q352] [n721] (by decide +kernel)
def v560 : Closed T 8 := rotateClosed n831 auto2 auto2ok
def v561 : Closed T 8 := rotateClosed n807 auto1 auto1ok
def v562 : Closed T 8 := rotateClosed n832 auto2 auto2ok
def v563 : Closed T 8 := rotateClosed n834 auto2 auto2ok
def n836 := cc 9 [w0,w1,w2,w9,w3,w4,w376,w5] [q106,q262,q333,q351,q352,q392] [n835,n833,v560,n807,v561,n830,v562,n722,n825,v563] (by decide +kernel)
def n837 := cc 8 [w385,w386,w0,w1,w2,w3,w4] [q309,q333,q351,q352,q403] [n723,n823] (by decide +kernel)
def n838 := cc 9 [w385,w0,w1,w2,w9,w3,w4,w5] [q167,q217,q226,q309,q333,q355] [n837,n724] (by decide +kernel)
def n839 := cc 8 [w0,w1,w73,w2,w3,w4,w5] [q20,q123,q284,q336,q351,q352] [] (by decide +kernel)
def v564 : Closed T 8 := rotateClosed n839 auto1 auto1ok
def n840 := cc 9 [w387,w0,w1,w2,w3,w4,w5] [q0,q106,q134,q217,q226,q355,q392,q420] [n754,n839,v564] (by decide +kernel)
def v565 : Closed T 8 := rotateClosed n837 auto2 auto2ok
def n841 := cc 9 [w387,w0,w1,w2,w9,w3,w4,w5] [q0,q92,q208,q214,q217,q352,q392] [v565,n725,n815,v550] (by decide +kernel)
def n842 := cc 8 [w0,w1,w2,w9,w3,w254,w388] [q168,q212,q221,q262,q333,q375] [n726] (by decide +kernel)
def v566 : Closed T 8 := rotateClosed n489 auto2 auto2ok
def v567 : Closed T 8 := rotateClosed n801 auto1 auto1ok
def v568 : Closed T 8 := rotateClosed n828 auto2 auto2ok
def n843 := cc 9 [w0,w1,w2,w9,w3,w254,w4,w5] [q106,q167,q214,q223,q262,q309,q333,q347,q350,q355,q420] [n489,v566,n727,n801,v567,n821,n828,v568,n842] (by decide +kernel)
def n844 := cc 8 [w0,w1,w2,w389,w3,w4,w5] [q106,q167,q168,q212,q221,q262,q375] [n728] (by decide +kernel)
def n845 := cc 8 [w390,w0,w1,w2,w3,w4,w5] [q106,q167,q262,q351,q352] [n729] (by decide +kernel)
def n846 := cc 9 [w0,w1,w2,w9,w3,w4,w5,w388] [q167,q214,q223,q262] [n845,n730,n844,n842] (by decide +kernel)
def n847 := cc 8 [w0,w1,w2,w419,w3,w4,w5] [q167,q176,q269,q309,q333,q351] [] (by decide +kernel)
def n848 := cc 8 [w0,w1,w2,w420,w3,w4,w5] [q106,q212,q262,q333,q375] [] (by decide +kernel)
def v569 : Closed T 8 := rotateClosed n848 auto2 auto2ok
def n849 := cc 9 [w360,w0,w1,w2,w9,w3,w4,w5] [q167,q217,q226,q262,q309,q333,q443] [n731,n819,v569,n847] (by decide +kernel)
def v570 : Closed T 9 := rotateClosed n580 auto2 auto2ok
def v571 : Closed T 9 := rotateClosed n814 auto1 auto1ok
def v572 : Closed T 9 := rotateClosed n814 auto2 auto2ok
def v573 : Closed T 9 := rotateClosed n814 auto3 auto3ok
def v574 : Closed T 9 := rotateClosed n838 auto2 auto2ok
def v575 : Closed T 9 := rotateClosed n349 auto2 auto2ok
def v576 : Closed T 9 := rotateClosed n849 auto2 auto2ok
def v577 : Closed T 9 := rotateClosed n271 auto2 auto2ok
def v578 : Closed T 9 := rotateClosed n177 auto1 auto1ok
def v579 : Closed T 9 := rotateClosed n177 auto2 auto2ok
def v580 : Closed T 9 := rotateClosed n177 auto3 auto3ok
def v581 : Closed T 9 := rotateClosed n797 auto2 auto2ok
def v582 : Closed T 9 := rotateClosed n589 auto2 auto2ok
def v583 : Closed T 9 := rotateClosed n381 auto2 auto2ok
def v584 : Closed T 9 := rotateClosed n796 auto2 auto2ok
def v585 : Closed T 9 := rotateClosed n841 auto2 auto2ok
def v586 : Closed T 9 := rotateClosed n840 auto2 auto2ok
def v587 : Closed T 9 := rotateClosed n147 auto1 auto1ok
def v588 : Closed T 9 := rotateClosed n147 auto2 auto2ok
def v589 : Closed T 9 := rotateClosed n147 auto3 auto3ok
def v590 : Closed T 9 := rotateClosed n799 auto1 auto1ok
def v591 : Closed T 9 := rotateClosed n798 auto1 auto1ok
def v592 : Closed T 9 := rotateClosed n818 auto1 auto1ok
def v593 : Closed T 9 := rotateClosed n818 auto2 auto2ok
def v594 : Closed T 9 := rotateClosed n818 auto3 auto3ok
def v595 : Closed T 9 := rotateClosed n40 auto1 auto1ok
def v596 : Closed T 9 := rotateClosed n40 auto2 auto2ok
def v597 : Closed T 9 := rotateClosed n40 auto3 auto3ok
def v598 : Closed T 9 := rotateClosed n787 auto2 auto2ok
def v599 : Closed T 9 := rotateClosed n286 auto2 auto2ok
def v600 : Closed T 9 := rotateClosed n490 auto2 auto2ok
def v601 : Closed T 9 := rotateClosed n805 auto1 auto1ok
def v602 : Closed T 9 := rotateClosed n805 auto2 auto2ok
def v603 : Closed T 9 := rotateClosed n805 auto3 auto3ok
def v604 : Closed T 9 := rotateClosed n87 auto1 auto1ok
def v605 : Closed T 9 := rotateClosed n87 auto2 auto2ok
def v606 : Closed T 9 := rotateClosed n87 auto3 auto3ok
def v607 : Closed T 9 := rotateClosed n829 auto2 auto2ok
def v608 : Closed T 9 := rotateClosed n820 auto2 auto2ok
def v609 : Closed T 9 := rotateClosed n794 auto2 auto2ok
def v610 : Closed T 9 := rotateClosed n308 auto2 auto2ok
def v611 : Closed T 9 := rotateClosed n812 auto1 auto1ok
def v612 : Closed T 9 := rotateClosed n812 auto2 auto2ok
def v613 : Closed T 9 := rotateClosed n812 auto3 auto3ok
def v614 : Closed T 9 := rotateClosed n836 auto2 auto2ok
def v615 : Closed T 9 := rotateClosed n555 auto2 auto2ok
def n850 := cc 10 [w0,w1,w2,w9,w3,w4,w5] [q19,q134,q228] [n580,v570,n814,v571,v572,v573,n838,v574,n349,v575,n849,v576,n271,v577,n177,v578,v579,v580,n797,v581,n589,v582,n381,v583,n796,v584,n841,v585,n840,v586,n147,v587,v588,v589,n799,v590,n643,v507,n798,v591,n818,v592,v593,v594,n40,v595,v596,v597,n787,v598,n204,n286,v599,n490,v600,n755,n746,v535,n732,n805,v601,v602,v603,n87,v604,v605,v606,n829,v607,n820,v608,n794,v609,n222,n843,n308,v610,n812,v611,v612,v613,n836,v614,n555,v615,n846] (by decide +kernel)
def n851 := cc 7 [w423,w1,w2,w3,w4,w5] [q72,q192,q375] [] (by decide +kernel)
def v616 : Closed T 7 := rotateClosed n851 auto1 auto1ok
def n852 := cc 8 [w424,w425,w1,w2,w3,w4,w5] [q20,q44,q62,q176,q375] [v616] (by decide +kernel)
def n853 := cc 9 [w424,w12,w0,w1,w2,w3,w4,w5] [q19,q176,q207,q352,q375] [n852,v84,n4] (by decide +kernel)
def n854 := cc 9 [w12,w0,w425,w1,w2,w3,w4,w5] [q8,q11,q62,q115,q176,q206] [n852] (by decide +kernel)
def n855 := cc 8 [w12,w0,w1,w2,w3,w4,w427] [q20,q44,q62,q176,q375] [] (by decide +kernel)
def n856 := cc 8 [w12,w0,w1,w2,w428,w3,w4] [q20,q44,q62,q375,q385,q413] [] (by decide +kernel)
def v617 : Closed T 7 := rotateClosed n851 auto3 auto3ok
def n857 := cc 8 [w429,w0,w1,w2,w430,w4,w5] [q62,q245,q262,q276,q314,q375,q407] [v617] (by decide +kernel)
def v618 : Closed T 8 := rotateClosed n96 auto2 auto2ok
def v619 : Closed T 8 := rotateClosed n856 auto2 auto2ok
def v620 : Closed T 8 := rotateClosed n855 auto2 auto2ok
def n858 := cc 9 [w429,w12,w0,w1,w2,w3,w4,w5] [q8,q228,q314,q352,q375] [n857,v618,v619,v620,n165] (by decide +kernel)
def v621 : Closed T 8 := rotateClosed n857 auto2 auto2ok
def n859 := cc 9 [w12,w431,w0,w1,w2,w3,w4,w5] [q11,q115,q176,q337,q338] [v621] (by decide +kernel)
def n860 := cc 9 [w0,w6,w1,w2,w3,w4,w5] [q8,q20,q136,q212,q215,q221,q224,q245,q329,q355,q420] [n641,v463,n7,v55,n644,n639,v386,n637] (by decide +kernel)
def v622 : Closed T 8 := rotateClosed n642 auto1 auto1ok
def n861 := cc 9 [w0,w1,w2,w9,w3,w4,w5] [q44,q167,q214,q217,q223,q226,q262,q333,q355,q420] [n7,v55,n642,v622,n644,n639,v386,n637] (by decide +kernel)
def n862 := cc 9 [w432,w0,w1,w2,w3,w4,w5] [q8,q11,q19,q134,q215,q226,q334,q355,q375,q407,q420] [v405,v557] (by decide +kernel)
def n863 := cc 8 [w12,w0,w358,w2,w3,w4,w5] [q8,q316,q352,q355,q375] [] (by decide +kernel)
def n864 := cc 8 [w12,w0,w1,w270,w3,w4,w5] [q8,q28,q281,q352,q385,q407] [] (by decide +kernel)
def n865 := cc 7 [w0,w1,w435,w2,w3,w5] [q123,q284,q336,q375] [] (by decide +kernel)
def v623 : Closed T 7 := rotateClosed n865 auto1 auto1ok
def n866 := cc 8 [w432,w0,w1,w2,w3,w436,w5] [q93,q115,q334,q352,q410] [v623] (by decide +kernel)
def v624 : Closed T 8 := rotateClosed n863 auto2 auto2ok
def n867 := cc 9 [w432,w12,w0,w1,w2,w3,w4,w5] [q8,q92,q207,q352,q375,q385,q407] [n866,v624,n864] (by decide +kernel)
def n868 := cc 9 [w12,w0,w1,w2,w3,w4,w436,w5] [q115,q212,q223,q276,q334,q420] [n866] (by decide +kernel)
def n869 := cc 8 [w12,w0,w1,w2,w438,w4,w5] [q20,q44,q62,q314,q375] [] (by decide +kernel)
def n870 := cc 8 [w12,w440,w1,w2,w3,w4,w5] [q136,q167,q176,q314,q375,q413] [] (by decide +kernel)
def n871 := cc 8 [w12,w0,w412,w2,w3,w4,w5] [q115,q276,q334,q352,q375] [] (by decide +kernel)
def n872 := cc 8 [w12,w0,w1,w396,w3,w4,w5] [q136,q176,q314,q334,q351,q352] [] (by decide +kernel)
def v625 : Closed T 7 := rotateClosed n865 auto3 auto3ok
def n873 := cc 8 [w439,w0,w1,w2,w441,w3,w4] [q176,q314,q334,q352,q363,q385,q413] [v625] (by decide +kernel)
def v626 : Closed T 8 := rotateClosed n871 auto2 auto2ok
def v627 : Closed T 8 := rotateClosed n869 auto2 auto2ok
def n874 := cc 9 [w439,w12,w0,w1,w2,w3,w4,w5] [q8,q314,q352,q355,q375] [n873,n870,v626,v627,n872] (by decide +kernel)
def n875 := cc 8 [w0,w1,w39,w2,w3,w393,w5] [q123,q284,q336,q375,q392,q427] [] (by decide +kernel)
def n876 := cc 8 [w0,w14,w1,w442,w2,w3,w4,w5] [q17,q26,q76,q154,q192,q208,q336,q356,q385] [] (by decide +kernel)
def n877 := cc 8 [w359,w0,w1,w2,w441,w3,w4] [q314,q334,q352,q355,q385,q400] [] (by decide +kernel)
def v628 : Closed T 8 := rotateClosed n877 auto3 auto3ok
def v629 : Closed T 8 := rotateClosed n876 auto2 auto2ok
def n878 := cc 9 [w0,w1,w39,w2,w3,w4,w5] [q19,q134,q214,q284,q293,q336,q341,q350,q355,q375,q392,q420] [v628,v389,n43,n494,v629,n875,n839] (by decide +kernel)
def v630 : Closed T 8 := rotateClosed n873 auto2 auto2ok
def n879 := cc 9 [w12,w0,w1,w2,w443,w3,w4,w5] [q62,q219,q223,q276,q293,q338,q347,q407] [v630] (by decide +kernel)
def n880 := cc 8 [w94,w12,w38,w0,w3,w4,w5] [] [] (by decide +kernel)
def n881 := cc 8 [w12,w38,w7,w0,w3,w4,w5] [] [] (by decide +kernel)
def n882 := cc 8 [w18,w12,w38,w0,w3,w4,w5] [] [] (by decide +kernel)
def v631 : Closed T 8 := rotateClosed n880 auto2 auto2ok
def v632 : Closed T 8 := rotateClosed n882 auto3 auto3ok
def v633 : Closed T 8 := rotateClosed n881 auto2 auto2ok
def n883 := cc 9 [w12,w38,w0,w1,w3,w4,w5] [q0,q8,q375,q385] [v631,v632,v633,n89,v463,n642,n736] (by decide +kernel)
def n884 := cc 9 [w12,w38,w0,w1,w2,w3,w4,w5] [q0,q8,q11,q17,q207,q208,q218,q219,q375,q385] [n747] (by decide +kernel)
def n885 := cc 8 [w12,w0,w14,w2,w3,w393,w5] [q93,q106,q115,q276,q334,q375,q397] [] (by decide +kernel)
def n886 := cc 9 [w12,w0,w14,w1,w2,w3,w4,w5] [q8,q92,q115,q207,q212,q214,q215,q352,q375,q420] [n885,n864] (by decide +kernel)
def n887 := cc 8 [w12,w392,w1,w2,w3,w4,w5] [q8,q136,q167,q176,q314,q334,q385] [] (by decide +kernel)
def n888 := cc 8 [w394,w12,w0,w1,w2,w4,w5] [q20,q44,q62,q314,q375] [] (by decide +kernel)
def v634 : Closed T 8 := rotateClosed n887 auto2 auto2ok
def v635 : Closed T 8 := rotateClosed n766 auto1 auto1ok
def n889 := cc 9 [w12,w0,w1,w2,w3,w4,w393,w5] [q115,q212,q223,q276,q334] [n888,v634,n885,v635] (by decide +kernel)
def n890 := cc 8 [w12,w0,w1,w444,w3,w4,w5] [q93,q106,q115,q276,q334,q375] [] (by decide +kernel)
def v636 : Closed T 8 := rotateClosed n890 auto2 auto2ok
def n891 := cc 9 [w359,w12,w0,w1,w2,w3,w4,w5] [q8,q226,q314,q334,q355,q385,q402] [n877,v636,n872,n646] (by decide +kernel)
def n892 := cc 9 [w12,w98,w0,w1,w2,w3,w4,w5] [q0,q77,q115,q176,q207,q223,q276,q347,q375,q397] [n760] (by decide +kernel)
def n893 := cc 8 [w12,w0,w1,w445,w2,w3,w4,w5] [q17,q34,q62,q223,q258,q276,q333,q334,q351,q434] [] (by decide +kernel)
def n894 := cc 8 [w12,w0,w1,w40,w3,w411,w5] [q93,q106,q115,q276,q334,q352,q375,q411] [] (by decide +kernel)
def n895 := cc 8 [w12,w0,w1,w40,w22,w3,w4,w5] [q17,q161,q218,q223,q375] [] (by decide +kernel)
def v637 : Closed T 8 := rotateClosed n876 auto1 auto1ok
def n896 := cc 9 [w12,w0,w1,w40,w2,w3,w4,w5] [q11,q17,q62,q161,q218,q219,q223,q228,q347,q375] [n45,n893,n895,n894,v637,n813] (by decide +kernel)
def n897 := cc 8 [w12,w446,w0,w2,w3,w4,w5] [q93,q115,q276,q334,q351,q352] [] (by decide +kernel)
def n898 := cc 8 [w12,w448,w1,w2,w3,w4,w5] [q136,q176,q314,q334,q352,q385,q413] [] (by decide +kernel)
def n899 := cc 8 [w394,w38,w0,w1,w2,w4,w5] [q20,q44,q72,q320,q375] [] (by decide +kernel)
def v638 : Closed T 8 := rotateClosed n899 auto1 auto1ok
def v639 : Closed T 8 := rotateClosed n898 auto2 auto2ok
def v640 : Closed T 8 := rotateClosed n875 auto1 auto1ok
def n900 := cc 9 [w12,w0,w1,w2,w3,w4,w411,w5] [q115,q212,q276,q334,q352,q407] [v638,n897,v639,n871,n894,v640,v564] (by decide +kernel)
def v641 : Closed T 8 := rotateClosed n800 auto1 auto1ok
def n901 := cc 9 [w359,w38,w0,w1,w2,w3,w4,w5] [q192,q217,q224,q320,q336,q385,q403] [v641] (by decide +kernel)
def n902 := cc 9 [w12,w15,w0,w1,w2,w3,w4,w5] [q11,q92,q212,q219,q221,q223,q226,q276,q375,q407,q411] [v624] (by decide +kernel)
def n903 := cc 8 [w12,w0,w1,w2,w3,w254,w388] [q93,q106,q177,q276,q334,q375] [] (by decide +kernel)
def v642 : Closed T 8 := rotateClosed n499 auto2 auto2ok
def n904 := cc 9 [w12,w0,w1,w2,w3,w254,w4,w5] [q115,q176,q223,q276,q314,q333,q347,q355,q375] [n499,v642,n893,n903] (by decide +kernel)
def n905 := cc 8 [w449,w0,w1,w2,w3,w4,w5] [q93,q115,q176,q276,q352] [] (by decide +kernel)
def n906 := cc 8 [w0,w1,w450,w2,w3,w4,w5] [q93,q106,q123,q192,q284,q375] [] (by decide +kernel)
def n907 := cc 8 [w12,w0,w1,w400,w3,w4,w5] [q93,q106,q176,q276,q375] [] (by decide +kernel)
def n908 := cc 8 [w12,w403,w0,w1,w3,w4,w5] [q93,q115,q176,q276,q351,q352] [] (by decide +kernel)
def v643 : Closed T 8 := rotateClosed n906 auto1 auto1ok
def n909 := cc 9 [w12,w0,w1,w2,w3,w4,w5,w388] [q176,q212,q223,q276] [n905,n908,n907,n903,v643] (by decide +kernel)
def n910 := cc 8 [w451,w0,w1,w2,w3,w4,w5] [q136,q167,q176,q282,q314,q334,q385] [] (by decide +kernel)
def n911 := cc 8 [w452,w0,w1,w2,w3,w4,w5] [q93,q115,q276,q334,q352] [] (by decide +kernel)
def v644 : Closed T 8 := rotateClosed n911 auto2 auto2ok
def n912 := cc 9 [w360,w12,w0,w1,w2,w3,w4,w5] [q176,q215,q226,q276,q314,q334,q444] [v644,n910] (by decide +kernel)
def v645 : Closed T 9 := rotateClosed n874 auto2 auto2ok
def v646 : Closed T 9 := rotateClosed n582 auto2 auto2ok
def v647 : Closed T 9 := rotateClosed n891 auto2 auto2ok
def v648 : Closed T 9 := rotateClosed n901 auto1 auto1ok
def v649 : Closed T 9 := rotateClosed n901 auto3 auto3ok
def v650 : Closed T 9 := rotateClosed n351 auto2 auto2ok
def v651 : Closed T 9 := rotateClosed n912 auto2 auto2ok
def v652 : Closed T 9 := rotateClosed n858 auto2 auto2ok
def v653 : Closed T 9 := rotateClosed n273 auto2 auto2ok
def v654 : Closed T 9 := rotateClosed n178 auto2 auto2ok
def v655 : Closed T 9 := rotateClosed n179 auto1 auto1ok
def v656 : Closed T 9 := rotateClosed n179 auto3 auto3ok
def v657 : Closed T 9 := rotateClosed n590 auto2 auto2ok
def v658 : Closed T 9 := rotateClosed n383 auto2 auto2ok
def v659 : Closed T 9 := rotateClosed n853 auto2 auto2ok
def v660 : Closed T 9 := rotateClosed n148 auto2 auto2ok
def v661 : Closed T 9 := rotateClosed n149 auto1 auto1ok
def v662 : Closed T 9 := rotateClosed n149 auto3 auto3ok
def v663 : Closed T 9 := rotateClosed n867 auto2 auto2ok
def v664 : Closed T 9 := rotateClosed n862 auto2 auto2ok
def v665 : Closed T 9 := rotateClosed n902 auto2 auto2ok
def v666 : Closed T 9 := rotateClosed n883 auto1 auto1ok
def v667 : Closed T 9 := rotateClosed n892 auto2 auto2ok
def v668 : Closed T 9 := rotateClosed n41 auto2 auto2ok
def v669 : Closed T 9 := rotateClosed n46 auto2 auto2ok
def v670 : Closed T 9 := rotateClosed n859 auto2 auto2ok
def v671 : Closed T 9 := rotateClosed n287 auto2 auto2ok
def v672 : Closed T 9 := rotateClosed n500 auto2 auto2ok
def v673 : Closed T 9 := rotateClosed n854 auto2 auto2ok
def v674 : Closed T 9 := rotateClosed n886 auto2 auto2ok
def v675 : Closed T 9 := rotateClosed n95 auto2 auto2ok
def v676 : Closed T 9 := rotateClosed n896 auto2 auto2ok
def v677 : Closed T 9 := rotateClosed n879 auto2 auto2ok
def v678 : Closed T 9 := rotateClosed n100 auto2 auto2ok
def v679 : Closed T 9 := rotateClosed n868 auto2 auto2ok
def v680 : Closed T 9 := rotateClosed n315 auto2 auto2ok
def v681 : Closed T 9 := rotateClosed n889 auto2 auto2ok
def v682 : Closed T 9 := rotateClosed n900 auto2 auto2ok
def v683 : Closed T 9 := rotateClosed n557 auto2 auto2ok
def v684 : Closed T 9 := rotateClosed n878 auto1 auto1ok
def v685 : Closed T 9 := rotateClosed n878 auto3 auto3ok
def n913 := cc 10 [w12,w0,w1,w2,w3,w4,w5] [q19,q134,q228] [n874,v645,n582,v646,n891,v647,v648,v649,n351,v650,n912,v651,n858,v652,n273,v653,n178,v654,v655,v656,n590,v657,n383,v658,n853,v659,n148,v660,v661,v662,n867,v663,n862,v664,n902,v665,n884,n883,v666,n892,v667,n41,v668,n46,v669,n859,v670,n205,n287,v671,n500,v672,n854,v673,n645,n640,n886,v674,n95,v675,n896,v676,n879,v677,n100,v678,n799,n228,n904,n868,v679,n315,v680,n889,v681,n900,v682,n557,v683,n909,n798,n860,v684,v685,n861] (by decide +kernel)
def n914 := cc 9 [w453,w0,w1,w40,w2,w3,w4,w5] [q17,q33,q92,q161,q223,q274,q420] [] (by decide +kernel)
def n915 := cc 8 [w0,w14,w1,w2,w81,w3,w4,w5] [q8,q207,q333,q375] [] (by decide +kernel)
def v686 : Closed T 8 := rotateClosed n864 auto1 auto1ok
def v687 : Closed T 8 := rotateClosed n756 auto1 auto1ok
def v688 : Closed T 8 := rotateClosed n915 auto3 auto3ok
def v689 : Closed T 8 := rotateClosed n120 auto3 auto3ok
def n916 := cc 9 [w0,w1,w2,w46,w3,w4,w5] [q0,q19,q106,q134,q208,q217,q228,q333,q348,q355,q420] [n185,n7,v686,n757,v687,v688,n6,v689] (by decide +kernel)
def n917 := cc 8 [w0,w14,w2,w270,w3,w393,w5] [q106,q262,q333,q375,q396,q420] [] (by decide +kernel)
def n918 := cc 8 [w0,w14,w1,w22,w2,w270,w3,w4,w5] [q333,q334,q336,q375,q431] [] (by decide +kernel)
def n919 := cc 8 [w0,w14,w1,w2,w454,w3,w4,w5] [q26,q154,q214,q228,q333,q356,q431] [] (by decide +kernel)
def v690 : Closed T 8 := rotateClosed n57 auto1 auto1ok
def n920 := cc 9 [w0,w14,w1,w2,w270,w3,w4,w5] [q8,q154,q207,q214,q223,q262,q333,q420] [v389,v690,n503,n918,n919,n917] (by decide +kernel)
def n921 := cc 8 [w41,w0,w1,w40,w2,w3,w4,w5] [q17,q106,q212,q218,q334] [] (by decide +kernel)
def v691 : Closed T 8 := rotateClosed n187 auto2 auto2ok
def n922 := cc 9 [w41,w0,w1,w2,w3,w4,w5] [q8,q92,q134,q176,q207,q212,q226,q228,q314,q355,q385,q420] [n584,v691,n7,n516,n649,n49,n921,n505,n121,n6] (by decide +kernel)
def n923 := cc 8 [w0,w14,w1,w456,w2,w3,w4,w5] [q26,q158,q286,q305,q336,q356,q438,q439] [] (by decide +kernel)
def n924 := cc 8 [w41,w0,w1,w22,w3,w4,w447] [q176,q314,q334,q355,q385,q414] [] (by decide +kernel)
def v692 : Closed T 8 := rotateClosed n923 auto3 auto3ok
def v693 : Closed T 8 := rotateClosed n809 auto2 auto2ok
def n925 := cc 9 [w41,w0,w1,w22,w2,w3,w4,w5] [q17,q176,q215,q216,q218,q221,q226,q258,q355] [n506,n924,v692,v693] (by decide +kernel)
def n926 := cc 9 [w0,w14,w1,w2,w3,w457,w4,w5] [q26,q214,q227,q228,q303,q420] [] (by decide +kernel)
def n927 := cc 8 [w15,w0,w72,w1,w40,w2,w3,w5] [q12,q17,q255,q328,q405,q430] [] (by decide +kernel)
def n928 := cc 8 [w15,w75,w0,w72,w1,w2,w3,w4] [q8,q81,q203,q288,q328,q351,q367,q405] [] (by decide +kernel)
def v694 : Closed T 8 := rotateClosed n928 auto3 auto3ok
def n929 := cc 9 [w15,w0,w1,w40,w2,w3,w5] [q11,q17,q328,q407,q420] [v694,n927] (by decide +kernel)
def n930 := cc 9 [w15,w0,w1,w2,w3,w4,w5] [q92,q221,q328,q352,q407] [v405,n839] (by decide +kernel)
def n931 := cc 8 [w0,w1,w2,w458,w3,w4,w5] [q62,q104,q163,q260,q307,q333,q351,q427] [] (by decide +kernel)
def n932 := cc 8 [w459,w0,w1,w2,w3,w4,w5] [q8,q17,q44,q261,q308,q334,q359] [] (by decide +kernel)
def v695 : Closed T 8 := rotateClosed n893 auto1 auto1ok
def v696 : Closed T 8 := rotateClosed n932 auto1 auto1ok
def v697 : Closed T 8 := rotateClosed n931 auto1 auto1ok
def n933 := cc 9 [w0,w410,w1,w2,w3,w4,w5] [q8,q19,q154,q255,q303,q328,q355,q420] [v695,v696,n801,v697] (by decide +kernel)
def n934 := cc 8 [w0,w1,w460,w2,w3,w4,w5] [q124,q136,q204,q336,q351,q392] [] (by decide +kernel)
def n935 := cc 8 [w0,w462,w1,w2,w3,w4,w5] [q8,q123,q292,q297,q329,q358] [] (by decide +kernel)
def v698 : Closed T 8 := rotateClosed n935 auto2 auto2ok
def n936 := cc 9 [w275,w0,w1,w2,w3,w4,w5] [q103,q203,q221,q226,q258,q323,q328,q420] [n517,v698,n934] (by decide +kernel)
def n937 := cc 9 [w275,w0,w1,w22,w2,w3,w4,w5] [q17,q203,q221,q226,q258,q323,q328,q355] [] (by decide +kernel)
def v699 : Closed T 8 := rotateClosed n924 auto3 auto3ok
def n938 := cc 9 [w0,w14,w2,w3,w393,w5] [q92,q228,q328,q392,q420] [v699,n917] (by decide +kernel)
def n939 := cc 8 [w392,w72,w1,w2,w3,w4] [q8,q134,q217,q295,q328] [] (by decide +kernel)
def v700 : Closed T 8 := rotateClosed n894 auto1 auto1ok
def v701 : Closed T 8 := rotateClosed n939 auto2 auto2ok
def n940 := cc 9 [w0,w14,w1,w2,w3,w393,w5] [q8,q92,q214,q228,q328,q392] [n885,v700,v701,n758,n802] (by decide +kernel)
def v702 : Closed T 8 := rotateClosed n895 auto1 auto1ok
def v703 : Closed T 8 := rotateClosed n921 auto1 auto1ok
def v704 : Closed T 8 := rotateClosed n921 auto3 auto3ok
def v705 : Closed T 8 := rotateClosed n915 auto2 auto2ok
def n941 := cc 9 [w0,w14,w72,w1,w2,w3,w4,w5] [q8,q207,q328,q355,q420] [v702,v703,v704,n915,v705] (by decide +kernel)
def n942 := cc 9 [w15,w0,w1,w22,w2,w3,w4,w5] [q11,q17,q221,q226,q258,q323,q328] [] (by decide +kernel)
def n943 := cc 8 [w0,w1,w2,w463,w3,w4,w5] [q100,q163,q212,q257,q307,q333,q375] [] (by decide +kernel)
def n944 := cc 8 [w0,w14,w1,w22,w2,w464,w3,w4,w5] [q333,q356,q431] [] (by decide +kernel)
def v706 : Closed T 8 := rotateClosed n927 auto1 auto1ok
def v707 : Closed T 8 := rotateClosed n927 auto2 auto2ok
def v708 : Closed T 8 := rotateClosed n508 auto3 auto3ok
def v709 : Closed T 8 := rotateClosed n918 auto3 auto3ok
def v710 : Closed T 8 := rotateClosed n943 auto1 auto1ok
def n945 := cc 9 [w0,w14,w1,w22,w2,w3,w4,w5] [q103,q154,q214,q215,q221,q226,q258,q303,q328,q355,q420] [v706,v707,n508,v708,n944,n918,v709,n803,v710] (by decide +kernel)
def n946 := cc 8 [w0,w1,w465,w2,w3,w4,w5] [q93,q130,q158,q336,q345] [] (by decide +kernel)
def v711 : Closed T 8 := rotateClosed n946 auto2 auto2ok
def n947 := cc 9 [w15,w0,w72,w1,w2,w3,w4,w5] [q8,q99,q203,q217,q225,q226,q255,q323,q328,q350,q355,q407] [n928,n514,n927,v711] (by decide +kernel)
def v712 : Closed T 9 := rotateClosed n585 auto2 auto2ok
def v713 : Closed T 9 := rotateClosed n189 auto1 auto1ok
def v714 : Closed T 9 := rotateClosed n158 auto1 auto1ok
def v715 : Closed T 9 := rotateClosed n914 auto1 auto1ok
def v716 : Closed T 9 := rotateClosed n896 auto1 auto1ok
def v717 : Closed T 9 := rotateClosed n925 auto3 auto3ok
def v718 : Closed T 9 := rotateClosed n922 auto3 auto3ok
def v719 : Closed T 9 := rotateClosed n947 auto2 auto2ok
def v720 : Closed T 9 := rotateClosed n929 auto1 auto1ok
def v721 : Closed T 9 := rotateClosed n942 auto3 auto3ok
def v722 : Closed T 9 := rotateClosed n930 auto1 auto1ok
def v723 : Closed T 9 := rotateClosed n937 auto3 auto3ok
def v724 : Closed T 9 := rotateClosed n936 auto3 auto3ok
def v725 : Closed T 9 := rotateClosed n59 auto1 auto1ok
def v726 : Closed T 9 := rotateClosed n518 auto2 auto2ok
def v727 : Closed T 9 := rotateClosed n916 auto1 auto1ok
def n948 := cc 10 [w0,w14,w1,w2,w3,w4,w5] [q19,q92,q134,q228,q328,q420] [v712,n275,n182,v713,n154,v714,v715,n862,n886,v716,v717,v718,v719,v720,v721,v722,v723,v724,n50,v725,n510,v726,n648,n759,n933,n941,n945,n920,n805,n926,n103,n123,n940,n938,v727] (by decide +kernel)
def n949 := cc 9 [w0,w412,w1,w2,w3,w4,w5] [q8,q92,q214,q228,q328,q407] [n871,v55,n108,n806,v557] (by decide +kernel)
def v728 : Closed T 8 := rotateClosed n897 auto1 auto1ok
def n950 := cc 9 [w413,w0,w1,w2,w3,w4,w5] [q92,q221,q228,q328,q352,q392] [v728,n7,n807,n108,n839] (by decide +kernel)
def v729 : Closed T 8 := rotateClosed n898 auto1 auto1ok
def n951 := cc 9 [w392,w1,w2,w3,w4,w5] [q134,q295,q328] [n887,v729,n761,n939,n810] (by decide +kernel)
def n952 := cc 9 [w394,w0,w1,w2,w4,w5] [q19,q92,q295] [n888,n899,n762,n811] (by decide +kernel)
def v730 : Closed T 9 := rotateClosed n900 auto1 auto1ok
def v731 : Closed T 9 := rotateClosed n951 auto2 auto2ok
def v732 : Closed T 9 := rotateClosed n949 auto1 auto1ok
def n953 := cc 10 [w0,w1,w2,w3,w4,w393,w5] [q92,q228,q328] [n952,n889,v730,v722,n950,v731,n763,n940,n938,v732,n812] (by decide +kernel)
def n954 := cc 9 [w0,w14,w1,w2,w3,w4,w5] [q8,q92,q214,q228,q328,q420] [v389,v557] (by decide +kernel)
def v733 : Closed T 8 := rotateClosed n872 auto1 auto1ok
def v734 : Closed T 8 := rotateClosed n764 auto1 auto1ok
def v735 : Closed T 8 := rotateClosed n672 auto1 auto1ok
def n955 := cc 9 [w0,w1,w467,w2,w3,w4,w5] [q134,q215,q295,q328,q351,q355] [n7,v733,v734,v735,n6] (by decide +kernel)
def v736 : Closed T 8 := rotateClosed n890 auto1 auto1ok
def n956 := cc 9 [w0,w352,w1,w2,w3,w4,w5] [q8,q92,q214,q228,q328,q420] [v736,n7,v389,n662,n6] (by decide +kernel)
def v737 : Closed T 9 := rotateClosed n954 auto2 auto2ok
def v738 : Closed T 9 := rotateClosed n956 auto3 auto3ok
def v739 : Closed T 9 := rotateClosed n955 auto1 auto1ok
def n957 := cc 10 [w359,w0,w1,w2,w3,w4,w5] [q134,q295,q328,q399] [n891,n901,n765,n814,v737,v738,v739] (by decide +kernel)
def n958 := cc 9 [w15,w468,w0,w1,w2,w3,w4,w5] [q92,q203,q221,q343] [] (by decide +kernel)
def n959 := cc 9 [w0,w1,w73,w2,w3,w4,w5] [q0,q19,q92,q123,q134,q208,q217,q350,q355,q375,q392,q420] [v55,n108,n104,v550] (by decide +kernel)
def n960 := cc 9 [w15,w0,w1,w73,w2,w3,w4,w5] [q11,q123,q350,q407] [v405] (by decide +kernel)
def v740 : Closed T 8 := rotateClosed n513 auto2 auto2ok
def n961 := cc 9 [w0,w358,w1,w2,w3,w4,w5] [q8,q19,q134,q136,q207,q212,q228,q329,q349,q350,q355,q420] [n863,v55,v740,n108,n817,n816] (by decide +kernel)
def n962 := cc 9 [w15,w0,w273,w1,w2,w3,w4,w5] [q11,q93,q350,q407] [n839] (by decide +kernel)
def n963 := cc 8 [w0,w1,w470,w2,w3,w4,w5] [q20,q130,q204,q291,q324,q336,q351,q352] [] (by decide +kernel)
def n964 := cc 8 [w0,w471,w1,w2,w3,w4,w5] [q131,q205,q292,q325,q329,q352,q375] [] (by decide +kernel)
def n965 := cc 9 [w469,w0,w1,w2,w3,w4,w5] [q129,q203,q290,q323,q328,q350,q352,q355] [n964,n963] (by decide +kernel)
def n966 := cc 8 [w0,w1,w2,w473,w3,w4,w5] [q110,q163,q176,q333,q351,q392] [] (by decide +kernel)
def n967 := cc 8 [w475,w0,w1,w2,w3,w4,w5] [q105,q106,q178,q261,q315,q334,q355,q385] [] (by decide +kernel)
def v741 : Closed T 8 := rotateClosed n967 auto3 auto3ok
def v742 : Closed T 8 := rotateClosed n966 auto1 auto1ok
def n968 := cc 9 [w0,w476,w1,w2,w3,w4,w5] [q128,q154,q214,q215,q287,q303,q328,q420] [v741,v742] (by decide +kernel)
def n969 := cc 9 [w15,w0,w1,w2,w474,w3,w4,w5] [q11,q103,q134,q221,q226,q407] [] (by decide +kernel)
def n970 := cc 8 [w477,w0,w1,w2,w3,w4,w5] [q131,q200,q212,q322,q329,q398] [] (by decide +kernel)
def v743 : Closed T 8 := rotateClosed n970 auto1 auto1ok
def n971 := cc 9 [w15,w75,w0,w1,w2,w3,w4,w5] [q128,q203,q214,q221,q226,q287,q323,q328,q347,q355,q405,q407,q412] [n928,v694,v743] (by decide +kernel)
def n972 := cc 9 [w15,w23,w0,w1,w2,w3,w4,w5] [q129,q203,q290,q323,q328,q350,q352,q355,q407] [] (by decide +kernel)
def v744 : Closed T 9 := rotateClosed n183 auto1 auto1ok
def v745 : Closed T 9 := rotateClosed n156 auto1 auto1ok
def v746 : Closed T 9 := rotateClosed n892 auto1 auto1ok
def v747 : Closed T 9 := rotateClosed n961 auto2 auto2ok
def v748 : Closed T 9 := rotateClosed n954 auto1 auto1ok
def v749 : Closed T 9 := rotateClosed n968 auto3 auto3ok
def n973 := cc 10 [w15,w0,w1,w2,w3,w4,w5] [q19,q92,q134,q228,q328,q407,q420] [n277,n191,v744,n840,n159,v745,n862,n902,v746,n965,n972,n971,n61,n51,n958,n515,n767,n962,n947,n960,n929,n942,n969,n818,n125,n107,v747,v748,v749,n959] (by decide +kernel)
def v750 : Closed T 8 := rotateClosed n903 auto1 auto1ok
def n974 := cc 9 [w0,w1,w2,w3,w254,w388] [q135,q228,q328] [n903,v750,n768,n842] (by decide +kernel)
def v751 : Closed T 9 := rotateClosed n904 auto1 auto1ok
def v752 : Closed T 9 := rotateClosed n965 auto1 auto1ok
def v753 : Closed T 9 := rotateClosed n546 auto2 auto2ok
def v754 : Closed T 9 := rotateClosed n933 auto1 auto1ok
def n975 := cc 10 [w0,w1,w2,w3,w254,w4,w5] [q92,q134,q228,q295,q328] [n904,v751,n965,v752,n546,v753,n769,n933,v754,n843,n974] (by decide +kernel)
def n976 := cc 8 [w0,w1,w2,w401,w3,w4,w5] [q17,q62,q106,q167,q262,q351] [n772] (by decide +kernel)
def n977 := cc 8 [w478,w0,w1,w2,w3,w4,w5] [q44,q93,q115,q176,q276,q375] [] (by decide +kernel)
def v755 : Closed T 8 := rotateClosed n907 auto1 auto1ok
def v756 : Closed T 8 := rotateClosed n977 auto1 auto1ok
def v757 : Closed T 8 := rotateClosed n976 auto1 auto1ok
def n978 := cc 9 [w0,w402,w1,w2,w3,w4,w5] [q8,q92,q134,q214,q228] [n905,v755,v756,n770,n773,v757] (by decide +kernel)
def n979 := cc 8 [w0,w1,w479,w2,w3,w4,w5] [q20,q123,q192,q284,q351,q352] [] (by decide +kernel)
def n980 := cc 8 [w0,w480,w1,w2,w3,w4,w5] [q93,q136,q245,q352,q375] [] (by decide +kernel)
def n981 := cc 9 [w403,w0,w1,w2,w3,w4,w5] [q92,q134,q221,q228,q352] [n845,n905,n908,n774,n980,n979] (by decide +kernel)
def v758 : Closed T 9 := rotateClosed n909 auto1 auto1ok
def v759 : Closed T 9 := rotateClosed n981 auto1 auto1ok
def v760 : Closed T 9 := rotateClosed n978 auto1 auto1ok
def n982 := cc 10 [w0,w1,w2,w3,w4,w5,w388] [q92,q134,q228] [n909,v758,n981,v759,n775,n978,v760,n846,n974] (by decide +kernel)
def n983 := cc 8 [w0,w482,w1,w2,w3,w4,w5] [q136,q292,q296,q329,q352,q375] [] (by decide +kernel)
def n984 := cc 8 [w484,w0,w1,w2,w3,w4,w5] [q20,q176,q289,q314,q334,q351,q352] [] (by decide +kernel)
def v761 : Closed T 8 := rotateClosed n911 auto3 auto3ok
def v762 : Closed T 8 := rotateClosed n983 auto1 auto1ok
def n985 := cc 9 [w0,w1,w483,w2,w3,w4,w5] [q134,q215,q295,q328,q351] [v761,n984,v762,n847] (by decide +kernel)
def n986 := cc 8 [w0,w1,w2,w486,w3,w4,w5] [q17,q62,q106,q262,q333,q351] [] (by decide +kernel)
def n987 := cc 8 [w488,w0,w1,w2,w3,w4,w5] [q44,q136,q176,q261,q314,q334,q385] [] (by decide +kernel)
def v763 : Closed T 8 := rotateClosed n987 auto3 auto3ok
def v764 : Closed T 8 := rotateClosed n986 auto1 auto1ok
def n988 := cc 9 [w0,w489,w1,w2,w3,w4,w5] [q8,q92,q214,q228,q328] [n911,v763,n777,v764] (by decide +kernel)
def v765 : Closed T 9 := rotateClosed n912 auto1 auto1ok
def v766 : Closed T 9 := rotateClosed n988 auto2 auto2ok
def v767 : Closed T 9 := rotateClosed n988 auto3 auto3ok
def v768 : Closed T 9 := rotateClosed n985 auto1 auto1ok
def n989 := cc 10 [w360,w0,w1,w2,w3,w4,w5] [q134,q228,q295,q328,q440] [n912,v765,n778,n849,v766,v767,n985,v768] (by decide +kernel)
def v769 : Closed T 10 := rotateClosed n586 auto2 auto2ok
def v770 : Closed T 10 := rotateClosed n957 auto1 auto1ok
def v771 : Closed T 10 := rotateClosed n957 auto2 auto2ok
def v772 : Closed T 10 := rotateClosed n957 auto3 auto3ok
def v773 : Closed T 10 := rotateClosed n352 auto2 auto2ok
def v774 : Closed T 10 := rotateClosed n989 auto2 auto2ok
def v775 : Closed T 10 := rotateClosed n278 auto2 auto2ok
def v776 : Closed T 10 := rotateClosed n194 auto1 auto1ok
def v777 : Closed T 10 := rotateClosed n194 auto2 auto2ok
def v778 : Closed T 10 := rotateClosed n194 auto3 auto3ok
def v779 : Closed T 10 := rotateClosed n591 auto2 auto2ok
def v780 : Closed T 10 := rotateClosed n384 auto2 auto2ok
def v781 : Closed T 10 := rotateClosed n163 auto1 auto1ok
def v782 : Closed T 10 := rotateClosed n163 auto2 auto2ok
def v783 : Closed T 10 := rotateClosed n163 auto3 auto3ok
def v784 : Closed T 10 := rotateClosed n913 auto1 auto1ok
def v785 : Closed T 10 := rotateClosed n973 auto1 auto1ok
def v786 : Closed T 10 := rotateClosed n973 auto2 auto2ok
def v787 : Closed T 10 := rotateClosed n973 auto3 auto3ok
def v788 : Closed T 10 := rotateClosed n72 auto1 auto1ok
def v789 : Closed T 10 := rotateClosed n72 auto2 auto2ok
def v790 : Closed T 10 := rotateClosed n72 auto3 auto3ok
def v791 : Closed T 10 := rotateClosed n288 auto2 auto2ok
def v792 : Closed T 10 := rotateClosed n547 auto2 auto2ok
def v793 : Closed T 10 := rotateClosed n948 auto1 auto1ok
def v794 : Closed T 10 := rotateClosed n948 auto2 auto2ok
def v795 : Closed T 10 := rotateClosed n948 auto3 auto3ok
def v796 : Closed T 10 := rotateClosed n126 auto1 auto1ok
def v797 : Closed T 10 := rotateClosed n126 auto2 auto2ok
def v798 : Closed T 10 := rotateClosed n126 auto3 auto3ok
def v799 : Closed T 10 := rotateClosed n324 auto2 auto2ok
def v800 : Closed T 10 := rotateClosed n953 auto1 auto1ok
def v801 : Closed T 10 := rotateClosed n953 auto2 auto2ok
def v802 : Closed T 10 := rotateClosed n953 auto3 auto3ok
def v803 : Closed T 10 := rotateClosed n564 auto2 auto2ok
def n990 := cc 11 [w0,w1,w2,w3,w4,w5] [] [n586,v769,n957,v770,v771,v772,n352,v773,n989,v774,n278,v775,n194,v776,v777,v778,n591,v779,n384,v780,n163,v781,v782,v783,n913,v784,n973,v785,v786,v787,n72,v788,v789,v790,n206,n288,v791,n547,v792,n779,n948,v793,v794,v795,n126,v796,v797,v798,n850,n237,n975,n324,v799,n953,v800,v801,v802,n564,v803,n982] (by decide +kernel)
theorem independentlyEnumeratedBound : Lower true R T 12 :=
  fromClosed n990 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 7, 6), (0xcccccccccccccccc, 7, 5), (0xf0f0f0f0f0f0f0f0, 7, 3), (0xff00ff00ff00ff00, 14, 6), (0xffff0000ffff0000, 26, 10), (0xffffffff00000000, 35, 3)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide +kernel)
end B51

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xfee8e8a8fc80c080
theorem fullBound : Lower true fullRoots fullWord 12 := by
  intro p bank h hit
  have hlow := B51.independentlyEnumeratedBound p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276676776 * 2 ^ 32 + 4236296320)
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_47887.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.and, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 18⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 12) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4236296320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4236296320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 18⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 13 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_47887

open PEqualNP.Outside.L_meta_47887 in
theorem PEqualNP.Outside.L_meta_47887 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4236296320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4236296320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact solve fullBound
