import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46966.Model
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

end PEqualNP.Outside.L_meta_46966.Model
namespace PEqualNP.Outside.L_meta_46966
open PEqualNP.Outside.L_meta_46966.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

namespace B27
def R : List Sig := vars 15
def T : Sig := 0xeee8eee8eee8eee8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B27

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

namespace B42
def R : List Sig := vars 31
def T : Sig := 0xfeeefeeafeeefeea
theorem low : Lower true R T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 17 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 2, 18)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B3.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 2, 18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide
  rw [he] at h
  exact h
end B42

namespace B49
def R : List Sig := vars 31
def T : Sig := 0xfefefee8fefefee8
theorem low : Lower true R T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 16 0) (raw := R)
    (T := T) (xs := [(0xffff0000ffff0000, 1, 17)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B5.low
  have he : (([(0xffff0000ffff0000, 1, 17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B49

namespace B51
def R : List Sig := vars 63
def T : Sig := 0xfeeefeeafeeae8a0
theorem s0 : Slice true R T 0xff00ff00ff00ff00 8 :=
  slice_correct (ms := [swapRows 83, swapRows 84] ++ fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B49.low
theorem s1 : Slice true R T 0xffff0000ffff0000 6 :=
  slice_correct (ms := [swapRows 84] ++ fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B42.low
theorem s2 : Slice true R T 0xffffffff00000000 6 :=
  slice_correct (ms := fixRows 0 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B42.low
theorem s3 : Slice true R T 0x4444444444444444 7 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 66, swapRows 83] ++ fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s4 : Slice true R T 0x505050505050505 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 5 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
theorem s5 : Slice true R T 0x5050505050505050 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s6 : Slice true R T 0x55005500550055 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 9 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
theorem s7 : Slice true R T 0x5500550055005500 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s8 : Slice true R T 0xc0c0c0c0c0c0c0c 7 :=
  slice_correct (ms := [swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 4 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s9 : Slice true R T 0x3300330033003300 5 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 83] ++ fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s10 : Slice true R T 0xcc00cc00cc00cc 7 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 83] ++ fixRows 8 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s11 : Slice true R T 0xcccc0000cccc 7 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 16 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s12 : Slice true R T 0xcccccccc 7 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67] ++ fixRows 32 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s13 : Slice true R T 0xf000f000f000f00 5 :=
  slice_correct (ms := [swapRows 66, swapRows 83] ++ fixRows 4 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s14 : Slice true R T 0xf0f00000f0f 5 :=
  slice_correct (ms := [swapRows 33, swapRows 66, swapRows 84] ++ fixRows 20 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s15 : Slice true R T 0xf0f00000f0f0 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67, swapRows 84] ++ fixRows 16 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s16 : Slice true R T 0xf0f0f0f 5 :=
  slice_correct (ms := [swapRows 33, swapRows 66] ++ fixRows 36 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s17 : Slice true R T 0xf0f0f0f0 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67] ++ fixRows 32 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s18 : Slice true R T 0xff000000ff00 7 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 16 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s19 : Slice true R T 0xff00ff00 7 :=
  slice_correct (ms := [swapRows 67] ++ fixRows 32 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s20 : Slice true R T 0xffff 5 :=
  slice_correct (ms := [swapRows 33] ++ fixRows 48 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s21 : Slice true R T 0xffff00000000 5 :=
  slice_correct (ms := fixRows 16 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s22 : Slice true R T 0xffff0000 5 :=
  slice_correct (ms := fixRows 32 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s24 : Slice true R T 0x404040404040404 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 82] ++ fixRows 5 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s33 : Slice true R T 0x444400004444 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 17 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s36 : Slice true R T 0x44444444 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 50, swapRows 67] ++ fixRows 33 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s44 : Slice true R T 0x505000005050 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66, swapRows 84] ++ fixRows 17 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s47 : Slice true R T 0x50505050 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66] ++ fixRows 33 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s50 : Slice true R T 0x550000005500 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 17 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s53 : Slice true R T 0x55005500 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 33 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s55 : Slice true R T 0x555500000000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50] ++ fixRows 17 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s56 : Slice true R T 0x55550000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50] ++ fixRows 33 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s62 : Slice true R T 0xc000c000c000c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66, swapRows 83, swapRows 84] ++ fixRows 12 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s66 : Slice true R T 0xc0c00000c0c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66, swapRows 84] ++ fixRows 20 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s70 : Slice true R T 0xc0c0c0c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66] ++ fixRows 36 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s74 : Slice true R T 0x330000003300 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 18 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s75 : Slice true R T 0xcc000000cc 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 24 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s79 : Slice true R T 0x33003300 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67] ++ fixRows 34 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s80 : Slice true R T 0xcc00cc 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67] ++ fixRows 40 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s86 : Slice true R T 0xcccc 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50] ++ fixRows 48 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s90 : Slice true R T 0xf0000000f00 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67, swapRows 84] ++ fixRows 20 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s94 : Slice true R T 0xf000f00 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67] ++ fixRows 36 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s105 : Slice true R T 0xff00 4 :=
  slice_correct (ms := fixRows 48 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def Pos : Nat → Bits
  | 0 => ((0xbb33729792d08d89 : BitVec 64) ++ (0xbb33729792d08d89 : BitVec 64))
  | 1 => ((0xd0f895656a6bb366 : BitVec 64) ++ (0xd0f895656a6bb366 : BitVec 64))
  | 2 => ((0x25ce596c25ac64bb : BitVec 64) ++ (0x25ce596c25ac64bb : BitVec 64))
  | 3 => ((0xca78a5b4d167396 : BitVec 64) ++ (0xca78a5b4d167396 : BitVec 64))
  | 4 => ((0xfc89ad12d5e79071 : BitVec 64) ++ (0xfc89ad12d5e79071 : BitVec 64))
  | 5 => ((0xc6552fa82b995e44 : BitVec 64) ++ (0xc6552fa82b995e44 : BitVec 64))
  | _ => 0
def Neg : Nat → Bits
  | 0 => ((0x30101180500888 : BitVec 64) ++ (0x30101180500888 : BitVec 64))
  | 1 => ((0x813814644a4b8322 : BitVec 64) ++ (0x813814644a4b8322 : BitVec 64))
  | 2 => ((0x234e416421a46411 : BitVec 64) ++ (0x234e416421a46411 : BitVec 64))
  | 3 => ((0x8878a1b44143386 : BitVec 64) ++ (0x8878a1b44143386 : BitVec 64))
  | 4 => ((0x74c1a90215a39071 : BitVec 64) ++ (0x74c1a90215a39071 : BitVec 64))
  | 5 => ((0xa6412f882b885444 : BitVec 64) ++ (0xa6412f882b885444 : BitVec 64))
  | _ => 0
theorem correctPairs : properPairs T (asRow Pos) (asRow Neg) := by unfold properPairs; decide +kernel
def auto1 : List Move := [swapRows 84]
theorem auto1ok : autoOK T auto1 = true := by decide +kernel
def w0 := inputObserved 63 Pos Neg 0
def w1 := inputObserved 63 Pos Neg 1
def w2 := inputObserved 63 Pos Neg 2
def w3 := inputObserved 63 Pos Neg 3
def w4 := inputObserved 63 Pos Neg 4
def w5 := inputObserved 63 Pos Neg 5
def w6 := combineObserved 0 w0 w1
def w7 := combineObserved 1 w6 w2
def w8 := combineObserved 1 w2 w3
def w9 := combineObserved 1 w2 w4
def w10 := combineObserved 1 w7 w4
def w11 := combineObserved 2 w7 w5
def w12 := combineObserved 1 w3 w4
def w13 := combineObserved 1 w4 w5
def w14 := combineObserved 1 w6 w5
def w15 := combineObserved 1 w2 w5
def w16 := combineObserved 1 w6 w4
def w17 := combineObserved 3 w2 w16
def w18 := combineObserved 1 w3 w5
def w19 := combineObserved 1 w16 w5
def w20 := combineObserved 2 w16 w5
def w21 := combineObserved 3 w6 w8
def w22 := combineObserved 3 w6 w9
def w23 := combineObserved 3 w6 w12
def w24 := combineObserved 3 w6 w13
def w25 := combineObserved 1 w0 w1
def w26 := combineObserved 2 w0 w1
def w27 := combineObserved 1 w26 w3
def w28 := combineObserved 3 w26 w3
def w29 := combineObserved 3 w0 w1
def w30 := combineObserved 2 w29 w2
def w31 := combineObserved 3 w30 w1
def w32 := combineObserved 1 w30 w4
def w33 := combineObserved 2 w30 w5
def w34 := combineObserved 2 w29 w5
def w35 := combineObserved 3 w34 w1
def w36 := combineObserved 1 w34 w2
def w37 := combineObserved 1 w34 w4
def w38 := combineObserved 2 w34 w4
def w39 := combineObserved 2 w1 w2
def w40 := combineObserved 2 w39 w5
def w41 := combineObserved 0 w1 w3
def w42 := combineObserved 1 w41 w2
def w43 := combineObserved 1 w41 w4
def w44 := combineObserved 1 w9 w5
def w45 := combineObserved 3 w0 w44
def w46 := combineObserved 2 w9 w5
def w47 := combineObserved 3 w2 w13
def w48 := combineObserved 1 w47 w41
def w49 := combineObserved 2 w1 w5
def w50 := combineObserved 2 w49 w4
def w51 := combineObserved 0 w29 w8
def w52 := combineObserved 0 w29 w9
def w53 := combineObserved 0 w29 w3
def w54 := combineObserved 0 w29 w12
def w55 := combineObserved 3 w2 w12
def w56 := combineObserved 0 w29 w13
def w57 := combineObserved 0 w0 w2
def w58 := combineObserved 1 w57 w1
def w59 := combineObserved 3 w57 w1
def w60 := combineObserved 0 w3 w4
def w61 := combineObserved 1 w60 w5
def w62 := combineObserved 0 w3 w5
def w63 := combineObserved 3 w62 w4
def w64 := combineObserved 3 w62 w18
def w65 := combineObserved 2 w3 w5
def w66 := combineObserved 3 w3 w5
def w67 := combineObserved 3 w3 w4
def w68 := combineObserved 0 w4 w5
def w69 := combineObserved 3 w68 w13
def w70 := combineObserved 2 w4 w5
def w71 := combineObserved 3 w4 w5
def w72 := combineObserved 1 w57 w3
def w73 := combineObserved 3 w57 w3
def w74 := combineObserved 1 w57 w5
def w75 := combineObserved 1 w60 w74
def w76 := combineObserved 1 w57 w4
def w77 := combineObserved 3 w62 w76
def w78 := combineObserved 0 w3 w76
def w79 := combineObserved 1 w78 w5
def w80 := combineObserved 0 w3 w74
def w81 := combineObserved 3 w80 w4
def w82 := combineObserved 1 w3 w74
def w83 := combineObserved 3 w80 w82
def w84 := combineObserved 1 w3 w76
def w85 := combineObserved 2 w3 w74
def w86 := combineObserved 3 w3 w74
def w87 := combineObserved 3 w3 w76
def w88 := combineObserved 0 w5 w76
def w89 := combineObserved 1 w4 w74
def w90 := combineObserved 3 w88 w89
def w91 := combineObserved 0 w4 w74
def w92 := combineObserved 2 w4 w74
def w93 := combineObserved 3 w4 w74
def w94 := combineObserved 3 w5 w76
def w95 := combineObserved 3 w68 w89
def w96 := combineObserved 3 w57 w4
def w97 := combineObserved 1 w57 w62
def w98 := combineObserved 3 w97 w18
def w99 := combineObserved 1 w57 w60
def w100 := combineObserved 1 w62 w4
def w101 := combineObserved 3 w57 w100
def w102 := combineObserved 1 w63 w57
def w103 := combineObserved 3 w57 w12
def w104 := combineObserved 1 w66 w57
def w105 := combineObserved 1 w67 w57
def w106 := combineObserved 1 w57 w68
def w107 := combineObserved 3 w106 w13
def w108 := combineObserved 3 w57 w13
def w109 := combineObserved 1 w69 w57
def w110 := combineObserved 1 w71 w57
def w111 := combineObserved 1 w70 w57
def w112 := combineObserved 1 w0 w3
def w113 := combineObserved 3 w2 w112
def w114 := combineObserved 1 w0 w2
def w115 := combineObserved 3 w0 w3
def w116 := combineObserved 1 w115 w2
def w117 := combineObserved 1 w115 w4
def w118 := combineObserved 2 w2 w5
def w119 := combineObserved 1 w114 w4
def w120 := combineObserved 2 w114 w5
def w121 := combineObserved 1 w0 w5
def w122 := combineObserved 3 w2 w121
def w123 := combineObserved 1 w0 w4
def w124 := combineObserved 3 w2 w123
def w125 := combineObserved 1 w123 w5
def w126 := combineObserved 3 w0 w4
def w127 := combineObserved 1 w126 w2
def w128 := combineObserved 3 w0 w5
def w129 := combineObserved 1 w128 w4
def w130 := combineObserved 1 w31 w4
def w131 := combineObserved 2 w31 w5
def w132 := combineObserved 3 w31 w12
def w133 := combineObserved 3 w31 w13
def w134 := combineObserved 0 w1 w13
def w135 := combineObserved 1 w0 w134
def w136 := combineObserved 1 w0 w41
def w137 := combineObserved 1 w136 w5
def w138 := combineObserved 1 w136 w4
def w139 := combineObserved 3 w2 w138
def w140 := combineObserved 0 w1 w119
def w141 := combineObserved 1 w114 w5
def w142 := combineObserved 1 w119 w5
def w143 := combineObserved 2 w119 w5
def w144 := combineObserved 1 w120 w4
def w145 := combineObserved 1 w41 w114
def w146 := combineObserved 3 w41 w114
def w147 := combineObserved 3 w41 w9
def w148 := combineObserved 3 w41 w13
def w149 := combineObserved 3 w41 w44
def w150 := combineObserved 3 w41 w119
def w151 := combineObserved 3 w41 w142
def w152 := combineObserved 1 w1 w3
def w153 := combineObserved 0 w151 w152
def w154 := combineObserved 2 w1 w3
def w155 := combineObserved 0 w1 w4
def w156 := combineObserved 1 w0 w155
def w157 := combineObserved 1 w155 w2
def w158 := combineObserved 1 w155 w114
def w159 := combineObserved 0 w1 w5
def w160 := combineObserved 3 w159 w114
def w161 := combineObserved 1 w159 w4
def w162 := combineObserved 2 w114 w4
def w163 := combineObserved 3 w0 w8
def w164 := combineObserved 3 w2 w3
def w165 := combineObserved 1 w164 w0
def w166 := combineObserved 0 w0 w9
def w167 := combineObserved 3 w0 w9
def w168 := combineObserved 0 w1 w9
def w169 := combineObserved 0 w114 w3
def w170 := combineObserved 0 w114 w4
def w171 := combineObserved 1 w170 w5
def w172 := combineObserved 0 w3 w9
def w173 := combineObserved 0 w114 w13
def w174 := combineObserved 3 w0 w15
def w175 := combineObserved 2 w2 w4
def w176 := combineObserved 3 w175 w114
def w177 := combineObserved 1 w118 w4
def w178 := combineObserved 2 w3 w4
def w179 := combineObserved 3 w2 w4
def w180 := combineObserved 1 w179 w0
def w181 := combineObserved 3 w2 w5
def w182 := combineObserved 1 w169 w4
def w183 := combineObserved 1 w114 w3
def w184 := combineObserved 3 w169 w183
def w185 := combineObserved 3 w169 w13
def w186 := combineObserved 0 w1 w183
def w187 := combineObserved 2 w114 w3
def w188 := combineObserved 3 w114 w3
def w189 := combineObserved 0 w114 w5
def w190 := combineObserved 1 w189 w4
def w191 := combineObserved 3 w189 w4
def w192 := combineObserved 3 w189 w141
def w193 := combineObserved 0 w3 w119
def w194 := combineObserved 0 w1 w142
def w195 := combineObserved 3 w162 w1
def w196 := combineObserved 2 w120 w4
def w197 := combineObserved 3 w114 w5
def w198 := combineObserved 3 w114 w4
def w199 := combineObserved 1 w0 w60
def w200 := combineObserved 1 w2 w60
def w201 := combineObserved 1 w114 w60
def w202 := combineObserved 2 w114 w62
def w203 := combineObserved 3 w0 w12
def w204 := combineObserved 0 w1 w12
def w205 := combineObserved 1 w0 w204
def w206 := combineObserved 2 w205 w2
def w207 := combineObserved 1 w204 w2
def w208 := combineObserved 1 w204 w114
def w209 := combineObserved 2 w208 w5
def w210 := combineObserved 0 w1 w18
def w211 := combineObserved 3 w210 w114
def w212 := combineObserved 0 w114 w12
def w213 := combineObserved 3 w114 w12
def w214 := combineObserved 1 w67 w2
def w215 := combineObserved 1 w67 w114
def w216 := combineObserved 3 w66 w114
def w217 := combineObserved 1 w2 w68
def w218 := combineObserved 1 w114 w68
def w219 := combineObserved 2 w114 w68
def w220 := combineObserved 3 w0 w13
def w221 := combineObserved 2 w135 w2
def w222 := combineObserved 1 w134 w2
def w223 := combineObserved 1 w134 w114
def w224 := combineObserved 3 w134 w114
def w225 := combineObserved 3 w114 w13
def w226 := combineObserved 0 w3 w13
def w227 := combineObserved 1 w0 w226
def w228 := combineObserved 2 w114 w226
def w229 := combineObserved 1 w70 w2
def w230 := combineObserved 1 w70 w114
def w231 := combineObserved 3 w71 w114
def w232 := combineObserved 2 w0 w2
def w233 := combineObserved 1 w232 w5
def w234 := combineObserved 1 w232 w4
def w235 := combineObserved 1 w234 w5
def w236 := combineObserved 2 w234 w5
def w237 := combineObserved 3 w0 w2
def w238 := combineObserved 1 w232 w60
def w239 := combineObserved 3 w232 w12
def w240 := combineObserved 1 w67 w232
def w241 := combineObserved 1 w232 w68
def w242 := combineObserved 3 w232 w13
def w243 := combineObserved 1 w70 w232
def w244 := combineObserved 1 w237 w4
def w245 := combineObserved 1 w237 w5
def w246 := combineObserved 1 w244 w5
def w247 := combineObserved 2 w244 w5
def w248 := combineObserved 3 w237 w9
def w249 := combineObserved 1 w237 w60
def w250 := combineObserved 3 w237 w12
def w251 := combineObserved 1 w67 w237
def w252 := combineObserved 1 w237 w68
def w253 := combineObserved 3 w237 w13
def w254 := combineObserved 1 w70 w237
def w255 := combineObserved 0 w0 w3
def w256 := combineObserved 1 w255 w2
def w257 := combineObserved 1 w256 w4
def w258 := combineObserved 2 w256 w5
def w259 := combineObserved 1 w255 w5
def w260 := combineObserved 1 w255 w4
def w261 := combineObserved 3 w2 w260
def w262 := combineObserved 1 w260 w5
def w263 := combineObserved 2 w260 w5
def w264 := combineObserved 3 w255 w112
def w265 := combineObserved 0 w264 w2
def w266 := combineObserved 1 w264 w2
def w267 := combineObserved 2 w264 w2
def w268 := combineObserved 3 w264 w2
def w269 := combineObserved 3 w255 w9
def w270 := combineObserved 1 w118 w255
def w271 := combineObserved 3 w255 w13
def w272 := combineObserved 0 w1 w2
def w273 := combineObserved 1 w0 w272
def w274 := combineObserved 3 w272 w112
def w275 := combineObserved 0 w39 w112
def w276 := combineObserved 0 w1 w112
def w277 := combineObserved 1 w276 w2
def w278 := combineObserved 3 w113 w1
def w279 := combineObserved 2 w0 w3
def w280 := combineObserved 1 w279 w1
def w281 := combineObserved 3 w279 w1
def w282 := combineObserved 1 w279 w2
def w283 := combineObserved 1 w116 w4
def w284 := combineObserved 2 w116 w5
def w285 := combineObserved 1 w115 w5
def w286 := combineObserved 3 w2 w117
def w287 := combineObserved 1 w117 w5
def w288 := combineObserved 2 w117 w5
def w289 := combineObserved 3 w115 w9
def w290 := combineObserved 3 w115 w1
def w291 := combineObserved 1 w118 w115
def w292 := combineObserved 1 w118 w0
def w293 := combineObserved 3 w115 w13
def w294 := combineObserved 0 w0 w4
def w295 := combineObserved 1 w294 w1
def w296 := combineObserved 0 w0 w5
def w297 := combineObserved 3 w296 w1
def w298 := combineObserved 0 w2 w4
def w299 := combineObserved 1 w298 w5
def w300 := combineObserved 0 w2 w5
def w301 := combineObserved 3 w300 w15
def w302 := combineObserved 3 w294 w1
def w303 := combineObserved 1 w294 w2
def w304 := combineObserved 1 w300 w4
def w305 := combineObserved 0 w303 w5
def w306 := combineObserved 1 w303 w5
def w307 := combineObserved 3 w305 w306
def w308 := combineObserved 1 w296 w2
def w309 := combineObserved 0 w308 w4
def w310 := combineObserved 1 w308 w4
def w311 := combineObserved 2 w303 w5
def w312 := combineObserved 3 w303 w5
def w313 := combineObserved 3 w308 w4
def w314 := combineObserved 3 w300 w306
def w315 := combineObserved 3 w296 w2
def w316 := combineObserved 1 w294 w3
def w317 := combineObserved 3 w296 w3
def w318 := combineObserved 3 w294 w3
def w319 := combineObserved 1 w296 w4
def w320 := combineObserved 1 w294 w5
def w321 := combineObserved 0 w2 w320
def w322 := combineObserved 3 w321 w306
def w323 := combineObserved 0 w2 w319
def w324 := combineObserved 2 w2 w320
def w325 := combineObserved 3 w2 w320
def w326 := combineObserved 3 w2 w319
def w327 := combineObserved 3 w296 w4
def w328 := combineObserved 3 w296 w121
def w329 := combineObserved 0 w2 w123
def w330 := combineObserved 1 w329 w5
def w331 := combineObserved 0 w2 w121
def w332 := combineObserved 3 w331 w4
def w333 := combineObserved 3 w296 w141
def w334 := combineObserved 2 w2 w121
def w335 := combineObserved 3 w294 w123
def w336 := combineObserved 0 w123 w5
def w337 := combineObserved 3 w336 w125
def w338 := combineObserved 3 w296 w125
def w339 := combineObserved 3 w121 w4
def w340 := combineObserved 2 w121 w4
def w341 := combineObserved 2 w123 w5
def w342 := combineObserved 1 w294 w300
def w343 := combineObserved 3 w342 w15
def w344 := combineObserved 1 w296 w298
def w345 := combineObserved 3 w296 w9
def w346 := combineObserved 1 w301 w294
def w347 := combineObserved 1 w175 w296
def w348 := combineObserved 1 w118 w294
def w349 := combineObserved 1 w181 w294
def w350 := combineObserved 0 w2 w3
def w351 := combineObserved 1 w0 w350
def w352 := combineObserved 3 w350 w13
def w353 := combineObserved 1 w126 w5
def w354 := combineObserved 1 w273 w5
def w355 := combineObserved 1 w273 w4
def w356 := combineObserved 3 w5 w355
def w357 := combineObserved 0 w1 w125
def w358 := combineObserved 3 w2 w125
def w359 := combineObserved 1 w272 w5
def w360 := combineObserved 3 w272 w123
def w361 := combineObserved 3 w272 w13
def w362 := combineObserved 3 w272 w125
def w363 := combineObserved 3 w272 w3
def w364 := combineObserved 0 w39 w123
def w365 := combineObserved 2 w145 w5
def w366 := combineObserved 3 w5 w138
def w367 := combineObserved 1 w122 w4
def w368 := combineObserved 1 w341 w2
def w369 := combineObserved 1 w41 w5
def w370 := combineObserved 3 w41 w123
def w371 := combineObserved 3 w41 w125
def w372 := combineObserved 1 w124 w41
def w373 := combineObserved 1 w358 w41
def w374 := combineObserved 3 w41 w368
def w375 := combineObserved 0 w1 w123
def w376 := combineObserved 1 w375 w2
def w377 := combineObserved 1 w35 w4
def w378 := combineObserved 2 w375 w5
def w379 := combineObserved 1 w155 w5
def w380 := combineObserved 1 w159 w123
def w381 := combineObserved 3 w159 w123
def w382 := combineObserved 1 w351 w5
def w383 := combineObserved 1 w351 w4
def w384 := combineObserved 3 w5 w383
def w385 := combineObserved 1 w350 w5
def w386 := combineObserved 3 w350 w123
def w387 := combineObserved 3 w350 w125
def w388 := combineObserved 1 w164 w123
def w389 := combineObserved 3 w164 w123
def w390 := combineObserved 3 w164 w125
def w391 := combineObserved 0 w2 w125
def w392 := combineObserved 3 w179 w123
def w393 := combineObserved 1 w181 w4
def w394 := combineObserved 3 w331 w141
def w395 := combineObserved 3 w122 w1
def w396 := combineObserved 2 w124 w5
def w397 := combineObserved 1 w300 w123
def w398 := combineObserved 3 w300 w123
def w399 := combineObserved 1 w0 w168
def w400 := combineObserved 2 w399 w5
def w401 := combineObserved 0 w123 w15
def w402 := combineObserved 3 w121 w9
def w403 := combineObserved 1 w175 w5
def w404 := combineObserved 1 w118 w123
def w405 := combineObserved 3 w175 w121
def w406 := combineObserved 1 w179 w5
def w407 := combineObserved 1 w181 w123
def w408 := combineObserved 3 w181 w123
def w409 := combineObserved 0 w3 w123
def w410 := combineObserved 2 w3 w121
def w411 := combineObserved 1 w62 w123
def w412 := combineObserved 3 w62 w123
def w413 := combineObserved 0 w0 w13
def w414 := combineObserved 0 w2 w13
def w415 := combineObserved 0 w4 w121
def w416 := combineObserved 3 w71 w121
def w417 := combineObserved 1 w70 w0
def w418 := combineObserved 3 w358 w1
def w419 := combineObserved 0 w3 w125
def w420 := combineObserved 3 w340 w1
def w421 := combineObserved 2 w0 w5
def w422 := combineObserved 1 w421 w2
def w423 := combineObserved 2 w0 w4
def w424 := combineObserved 1 w423 w2
def w425 := combineObserved 1 w422 w4
def w426 := combineObserved 2 w424 w5
def w427 := combineObserved 1 w421 w4
def w428 := combineObserved 1 w423 w5
def w429 := combineObserved 3 w2 w427
def w430 := combineObserved 3 w298 w9
def w431 := combineObserved 1 w421 w350
def w432 := combineObserved 1 w421 w164
def w433 := combineObserved 1 w421 w298
def w434 := combineObserved 3 w0 w299
def w435 := combineObserved 3 w423 w15
def w436 := combineObserved 1 w423 w118
def w437 := combineObserved 1 w421 w179
def w438 := combineObserved 1 w421 w60
def w439 := combineObserved 3 w0 w61
def w440 := combineObserved 1 w128 w2
def w441 := combineObserved 1 w440 w4
def w442 := combineObserved 2 w127 w5
def w443 := combineObserved 3 w2 w129
def w444 := combineObserved 3 w128 w15
def w445 := combineObserved 1 w128 w298
def w446 := combineObserved 3 w128 w9
def w447 := combineObserved 1 w118 w126
def w448 := combineObserved 1 w181 w126
def w449 := combineObserved 3 w128 w13
def w450 := combineObserved 1 w273 w3
def w451 := combineObserved 1 w355 w5
def w452 := combineObserved 2 w273 w5
def w453 := combineObserved 3 w273 w12
def w454 := combineObserved 3 w273 w13
def w455 := combineObserved 1 w272 w4
def w456 := combineObserved 3 w0 w455
def w457 := combineObserved 1 w455 w5
def w458 := combineObserved 2 w455 w5
def w459 := combineObserved 1 w1 w2
def w460 := combineObserved 3 w272 w12
def w461 := combineObserved 1 w361 w0
def w462 := combineObserved 0 w459 w3
def w463 := combineObserved 2 w459 w3
def w464 := combineObserved 1 w40 w0
def w465 := combineObserved 0 w1 w15
def w466 := combineObserved 1 w40 w4
def w467 := combineObserved 2 w40 w4
def w468 := combineObserved 0 w39 w12
def w469 := combineObserved 0 w39 w13
def w470 := combineObserved 3 w1 w2
def w471 := combineObserved 1 w145 w4
def w472 := combineObserved 2 w471 w5
def w473 := combineObserved 2 w136 w2
def w474 := combineObserved 1 w138 w5
def w475 := combineObserved 3 w2 w474
def w476 := combineObserved 2 w136 w5
def w477 := combineObserved 3 w136 w9
def w478 := combineObserved 3 w136 w44
def w479 := combineObserved 1 w46 w0
def w480 := combineObserved 3 w136 w13
def w481 := combineObserved 1 w47 w0
def w482 := combineObserved 1 w47 w136
def w483 := combineObserved 3 w0 w42
def w484 := combineObserved 1 w42 w4
def w485 := combineObserved 2 w42 w5
def w486 := combineObserved 3 w0 w43
def w487 := combineObserved 3 w2 w43
def w488 := combineObserved 1 w43 w5
def w489 := combineObserved 2 w43 w5
def w490 := combineObserved 3 w41 w152
def w491 := combineObserved 1 w174 w4
def w492 := combineObserved 3 w41 w491
def w493 := combineObserved 1 w147 w0
def w494 := combineObserved 1 w148 w0
def w495 := combineObserved 1 w149 w0
def w496 := combineObserved 0 w1 w44
def w497 := combineObserved 1 w220 w2
def w498 := combineObserved 3 w41 w497
def w499 := combineObserved 3 w0 w48
def w500 := combineObserved 3 w1 w3
def w501 := combineObserved 2 w156 w2
def w502 := combineObserved 2 w156 w5
def w503 := combineObserved 3 w0 w157
def w504 := combineObserved 1 w159 w2
def w505 := combineObserved 1 w504 w4
def w506 := combineObserved 2 w157 w5
def w507 := combineObserved 3 w0 w161
def w508 := combineObserved 3 w2 w161
def w509 := combineObserved 3 w159 w9
def w510 := combineObserved 1 w1 w4
def w511 := combineObserved 1 w50 w0
def w512 := combineObserved 1 w50 w2
def w513 := combineObserved 0 w49 w9
def w514 := combineObserved 3 w1 w4
def w515 := combineObserved 1 w514 w5
def w516 := combineObserved 3 w1 w5
def w517 := combineObserved 3 w516 w4
def w518 := combineObserved 1 w383 w5
def w519 := combineObserved 0 w1 w518
def w520 := combineObserved 2 w351 w5
def w521 := combineObserved 2 w0 w13
def w522 := combineObserved 3 w351 w13
def w523 := combineObserved 1 w350 w4
def w524 := combineObserved 3 w0 w523
def w525 := combineObserved 1 w523 w5
def w526 := combineObserved 2 w523 w5
def w527 := combineObserved 1 w521 w350
def w528 := combineObserved 1 w352 w0
def w529 := combineObserved 3 w163 w1
def w530 := combineObserved 0 w1 w8
def w531 := combineObserved 1 w0 w530
def w532 := combineObserved 2 w2 w3
def w533 := combineObserved 1 w532 w0
def w534 := combineObserved 2 w165 w5
def w535 := combineObserved 1 w164 w4
def w536 := combineObserved 3 w0 w535
def w537 := combineObserved 1 w164 w5
def w538 := combineObserved 1 w535 w5
def w539 := combineObserved 2 w535 w5
def w540 := combineObserved 3 w164 w13
def w541 := combineObserved 1 w0 w540
def w542 := combineObserved 1 w0 w298
def w543 := combineObserved 0 w542 w9
def w544 := combineObserved 1 w0 w300
def w545 := combineObserved 3 w544 w15
def w546 := combineObserved 2 w542 w5
def w547 := combineObserved 0 w0 w299
def w548 := combineObserved 3 w547 w1
def w549 := combineObserved 3 w547 w3
def w550 := combineObserved 0 w0 w304
def w551 := combineObserved 1 w298 w121
def w552 := combineObserved 2 w0 w299
def w553 := combineObserved 1 w552 w434
def w554 := combineObserved 3 w0 w304
def w555 := combineObserved 3 w300 w4
def w556 := combineObserved 0 w0 w15
def w557 := combineObserved 3 w556 w1
def w558 := combineObserved 3 w556 w3
def w559 := combineObserved 1 w556 w4
def w560 := combineObserved 1 w166 w5
def w561 := combineObserved 3 w556 w4
def w562 := combineObserved 1 w430 w0
def w563 := combineObserved 3 w300 w141
def w564 := combineObserved 2 w0 w9
def w565 := combineObserved 1 w564 w298
def w566 := combineObserved 2 w0 w15
def w567 := combineObserved 1 w566 w174
def w568 := combineObserved 0 w301 w0
def w569 := combineObserved 3 w568 w1
def w570 := combineObserved 3 w568 w3
def w571 := combineObserved 1 w568 w4
def w572 := combineObserved 3 w568 w4
def w573 := combineObserved 1 w301 w0
def w574 := combineObserved 3 w301 w0
def w575 := combineObserved 0 w301 w4
def w576 := combineObserved 1 w301 w4
def w577 := combineObserved 3 w575 w576
def w578 := combineObserved 2 w430 w5
def w579 := combineObserved 3 w430 w5
def w580 := combineObserved 3 w301 w4
def w581 := combineObserved 0 w4 w15
def w582 := combineObserved 2 w4 w15
def w583 := combineObserved 3 w300 w44
def w584 := combineObserved 0 w9 w5
def w585 := combineObserved 3 w584 w44
def w586 := combineObserved 3 w4 w15
def w587 := combineObserved 3 w9 w5
def w588 := combineObserved 1 w587 w298
def w589 := combineObserved 3 w174 w1
def w590 := combineObserved 1 w399 w5
def w591 := combineObserved 1 w465 w4
def w592 := combineObserved 1 w0 w172
def w593 := combineObserved 1 w172 w5
def w594 := combineObserved 2 w3 w15
def w595 := combineObserved 1 w62 w9
def w596 := combineObserved 3 w62 w9
def w597 := combineObserved 3 w71 w15
def w598 := combineObserved 1 w0 w496
def w599 := combineObserved 0 w3 w44
def w600 := combineObserved 3 w586 w1
def w601 := combineObserved 1 w175 w0
def w602 := combineObserved 2 w601 w5
def w603 := combineObserved 3 w0 w177
def w604 := combineObserved 1 w118 w60
def w605 := combineObserved 3 w2 w61
def w606 := combineObserved 2 w180 w5
def w607 := combineObserved 3 w0 w393
def w608 := combineObserved 3 w181 w13
def w609 := combineObserved 3 w2 w199
def w610 := combineObserved 2 w199 w5
def w611 := combineObserved 3 w0 w200
def w612 := combineObserved 2 w200 w5
def w613 := combineObserved 0 w0 w61
def w614 := combineObserved 3 w613 w1
def w615 := combineObserved 0 w0 w100
def w616 := combineObserved 1 w615 w2
def w617 := combineObserved 3 w613 w2
def w618 := combineObserved 1 w60 w121
def w619 := combineObserved 2 w0 w61
def w620 := combineObserved 3 w0 w100
def w621 := combineObserved 0 w2 w100
def w622 := combineObserved 1 w0 w621
def w623 := combineObserved 0 w2 w61
def w624 := combineObserved 1 w60 w15
def w625 := combineObserved 3 w623 w624
def w626 := combineObserved 2 w2 w61
def w627 := combineObserved 3 w2 w100
def w628 := combineObserved 3 w0 w18
def w629 := combineObserved 3 w628 w1
def w630 := combineObserved 1 w203 w2
def w631 := combineObserved 3 w0 w208
def w632 := combineObserved 1 w55 w0
def w633 := combineObserved 3 w2 w18
def w634 := combineObserved 3 w633 w1
def w635 := combineObserved 1 w67 w0
def w636 := combineObserved 2 w635 w2
def w637 := combineObserved 3 w0 w214
def w638 := combineObserved 1 w0 w68
def w639 := combineObserved 3 w2 w638
def w640 := combineObserved 1 w414 w638
def w641 := combineObserved 0 w638 w13
def w642 := combineObserved 3 w638 w13
def w643 := combineObserved 3 w0 w217
def w644 := combineObserved 1 w0 w414
def w645 := combineObserved 0 w217 w13
def w646 := combineObserved 3 w217 w13
def w647 := combineObserved 3 w413 w1
def w648 := combineObserved 1 w413 w2
def w649 := combineObserved 3 w413 w2
def w650 := combineObserved 3 w413 w3
def w651 := combineObserved 3 w68 w125
def w652 := combineObserved 1 w69 w0
def w653 := combineObserved 1 w521 w68
def w654 := combineObserved 3 w414 w44
def w655 := combineObserved 2 w654 w68
def w656 := combineObserved 3 w68 w44
def w657 := combineObserved 1 w69 w2
def w658 := combineObserved 2 w2 w13
def w659 := combineObserved 1 w658 w68
def w660 := combineObserved 0 w69 w0
def w661 := combineObserved 3 w660 w1
def w662 := combineObserved 1 w660 w2
def w663 := combineObserved 3 w660 w2
def w664 := combineObserved 3 w660 w3
def w665 := combineObserved 3 w69 w0
def w666 := combineObserved 0 w69 w2
def w667 := combineObserved 1 w666 w0
def w668 := combineObserved 3 w69 w2
def w669 := combineObserved 3 w413 w125
def w670 := combineObserved 1 w521 w2
def w671 := combineObserved 3 w220 w1
def w672 := combineObserved 3 w0 w223
def w673 := combineObserved 3 w47 w1
def w674 := combineObserved 1 w2 w226
def w675 := combineObserved 2 w3 w13
def w676 := combineObserved 2 w417 w2
def w677 := combineObserved 3 w0 w229
def x0 : Sig := 0xaaaaaaaaaaaaaaaa
def x1 : Sig := 0xcccccccccccccccc
def x2 : Sig := 0x8888888888888888
def x3 : Sig := 0xf0f0f0f0f0f0f0f0
def x4 : Sig := 0xffffffff00000000
def x5 : Sig := 0xa0a0a0a0a0a0a0a0
def x6 : Sig := 0xffff0000ffff0000
def x7 : Sig := 0xaaaaaaaa00000000
def x8 : Sig := 0xc0c0c0c0c0c0c0c0
def x9 : Sig := 0xcccc0000cccc0000
def x10 : Sig := 0xffff000000000000
def x11 : Sig := 0xeeeeeeeeeeeeeeee
def x12 : Sig := 0xfafafafafafafafa
def x13 : Sig := 0xffffaaaaffffaaaa
def x14 : Sig := 0xfcfcfcfcfcfcfcfc
def x15 : Sig := 0xfffff0f0fffff0f0
def x16 : Sig := 0xffffffffffff0000
def x17 : Sig := 0xa0a0a0a0a0a0a0a
def x18 : Sig := 0xcccc0000cccc
def x19 : Sig := 0x4444444444444444
def x20 : Sig := 0x5555000055550000
def x21 : Sig := 0xf0f00000f0f0000
def x22 : Sig := 0xf0f0f0f00000000
def x23 : Sig := 0xff00ff00ff00ff00
def x24 : Sig := 0xcc00cc00cc00cc00
def x25 : Sig := 0xf000f000f000f000
def x26 : Sig := 0xf0f00000f0f00000
def x27 : Sig := 0xf0f0f0f000000000
def x28 : Sig := 0xff000000ff000000
def x29 : Sig := 0xff00ff0000000000
def x30 : Sig := 0xfff0fff0fff0fff0
def x31 : Sig := 0xffffff00ffffff00
def x32 : Sig := 0xf000f000f000f0
def x33 : Sig := 0xf0f00000f0f0
def x34 : Sig := 0xf0f0f0f0
def x35 : Sig := 0xff000000ff0000
def x36 : Sig := 0xff00ff00000000
def x37 : Sig := 0xaaaa0000aaaa0000
def x38 : Sig := 0xffaaffaaffaaffaa
def x39 : Sig := 0xffffffffaaaaaaaa
def x40 : Sig := 0xaa00aa00aa00aa
def x41 : Sig := 0xaaaa0000aaaa
def x42 : Sig := 0xaaaaaaaa
def x43 : Sig := 0xffff0000
def x44 : Sig := 0x5500550055005500
def x45 : Sig := 0x5555555500000000
def x46 : Sig := 0x5050505050505050
def x47 : Sig := 0xfffffffff0f0f0f0
def x48 : Sig := 0xf000f000f000f00
def x49 : Sig := 0xcccccccc00000000
def x50 : Sig := 0xcccccccc
def p0 := prefixPool s0 [] (by decide +kernel)
def p1 := prefixPool s0 [(0,x0,x1),(1,x2,x3)] (by decide +kernel)
def p2 := prefixPool s0 [(0,x0,x1),(1,x2,x4)] (by decide +kernel)
def p3 := prefixPool s0 [(0,x0,x3)] (by decide +kernel)
def p4 := prefixPool s0 [(0,x0,x3),(1,x5,x6)] (by decide +kernel)
def p5 := prefixPool s0 [(0,x0,x3),(1,x5,x4)] (by decide +kernel)
def p6 := prefixPool s0 [(0,x0,x3),(3,x5,x1)] (by decide +kernel)
def p7 := prefixPool s0 [(0,x0,x3),(3,x5,x1),(1,x6,x4)] (by decide +kernel)
def p8 := prefixPool s0 [(0,x0,x6)] (by decide +kernel)
def p9 := prefixPool s0 [(0,x0,x4),(3,x7,x1)] (by decide +kernel)
def p10 := prefixPool s0 [(0,x1,x3)] (by decide +kernel)
def p11 := prefixPool s0 [(0,x1,x3),(0,x8,x6)] (by decide +kernel)
def p12 := prefixPool s0 [(0,x1,x3),(0,x8,x4)] (by decide +kernel)
def p13 := prefixPool s0 [(0,x1,x3),(1,x0,x1),(1,x1,x3)] (by decide +kernel)
def p14 := prefixPool s0 [(0,x1,x3),(1,x8,x0)] (by decide +kernel)
def p15 := prefixPool s0 [(0,x1,x3),(1,x8,x0),(1,x1,x3)] (by decide +kernel)
def p16 := prefixPool s0 [(0,x1,x3),(1,x8,x4)] (by decide +kernel)
def p17 := prefixPool s0 [(0,x1,x3),(1,x1,x3)] (by decide +kernel)
def p18 := prefixPool s0 [(0,x1,x6),(1,x9,x3)] (by decide +kernel)
def p19 := prefixPool s0 [(0,x6,x4),(1,x10,x0),(1,x6,x4)] (by decide +kernel)
def p20 := prefixPool s0 [(0,x6,x4),(1,x6,x4)] (by decide +kernel)
def p21 := prefixPool s0 [(1,x0,x1)] (by decide +kernel)
def p22 := prefixPool s0 [(1,x0,x1),(0,x0,x1),(1,x2,x3)] (by decide +kernel)
def p23 := prefixPool s0 [(1,x0,x1),(1,x0,x3)] (by decide +kernel)
def p24 := prefixPool s0 [(1,x0,x1),(1,x0,x6)] (by decide +kernel)
def p25 := prefixPool s0 [(1,x0,x1),(1,x0,x4),(1,x6,x4)] (by decide +kernel)
def p26 := prefixPool s0 [(1,x0,x1),(1,x11,x3)] (by decide +kernel)
def p27 := prefixPool s0 [(1,x0,x1),(3,x11,x3)] (by decide +kernel)
def p28 := prefixPool s0 [(1,x0,x3)] (by decide +kernel)
def p29 := prefixPool s0 [(1,x0,x3),(0,x12,x1)] (by decide +kernel)
def p30 := prefixPool s0 [(1,x0,x3),(0,x12,x1),(1,x0,x1)] (by decide +kernel)
def p31 := prefixPool s0 [(1,x0,x3),(0,x12,x1),(1,x0,x1),(1,x1,x3)] (by decide +kernel)
def p32 := prefixPool s0 [(1,x0,x3),(1,x3,x6)] (by decide +kernel)
def p33 := prefixPool s0 [(1,x0,x3),(1,x3,x6),(1,x6,x4)] (by decide +kernel)
def p34 := prefixPool s0 [(1,x0,x3),(1,x12,x6)] (by decide +kernel)
def p35 := prefixPool s0 [(1,x0,x3),(1,x12,x6),(1,x6,x4)] (by decide +kernel)
def p36 := prefixPool s0 [(1,x0,x3),(1,x6,x4)] (by decide +kernel)
def p37 := prefixPool s0 [(1,x0,x3),(2,x12,x1)] (by decide +kernel)
def p38 := prefixPool s0 [(1,x0,x3),(2,x12,x6)] (by decide +kernel)
def p39 := prefixPool s0 [(1,x0,x3),(2,x12,x4)] (by decide +kernel)
def p40 := prefixPool s0 [(1,x0,x6)] (by decide +kernel)
def p41 := prefixPool s0 [(1,x0,x6),(0,x13,x1)] (by decide +kernel)
def p42 := prefixPool s0 [(1,x0,x6),(1,x3,x6)] (by decide +kernel)
def p43 := prefixPool s0 [(1,x0,x6),(1,x13,x4)] (by decide +kernel)
def p44 := prefixPool s0 [(1,x0,x6),(2,x13,x1)] (by decide +kernel)
def p45 := prefixPool s0 [(1,x0,x6),(2,x13,x4)] (by decide +kernel)
def p46 := prefixPool s0 [(1,x0,x4),(1,x6,x4)] (by decide +kernel)
def p47 := prefixPool s0 [(1,x1,x3),(1,x14,x6)] (by decide +kernel)
def p48 := prefixPool s0 [(1,x3,x6)] (by decide +kernel)
def p49 := prefixPool s0 [(1,x3,x6),(0,x15,x1)] (by decide +kernel)
def p50 := prefixPool s0 [(1,x3,x6),(1,x6,x4)] (by decide +kernel)
def p51 := prefixPool s0 [(1,x3,x6),(1,x15,x4)] (by decide +kernel)
def p52 := prefixPool s0 [(1,x3,x6),(2,x15,x0)] (by decide +kernel)
def p53 := prefixPool s0 [(1,x3,x6),(2,x15,x1)] (by decide +kernel)
def p54 := prefixPool s0 [(1,x3,x6),(2,x15,x1),(1,x6,x4)] (by decide +kernel)
def p55 := prefixPool s0 [(1,x3,x6),(2,x15,x4)] (by decide +kernel)
def p56 := prefixPool s0 [(1,x3,x4)] (by decide +kernel)
def p57 := prefixPool s0 [(1,x3,x4),(1,x6,x4)] (by decide +kernel)
def p58 := prefixPool s0 [(1,x6,x4)] (by decide +kernel)
def p59 := prefixPool s0 [(1,x6,x4),(0,x16,x1)] (by decide +kernel)
def p60 := prefixPool s0 [(1,x6,x4),(0,x16,x3)] (by decide +kernel)
def p61 := prefixPool s0 [(1,x6,x4),(2,x16,x0)] (by decide +kernel)
def p62 := prefixPool s0 [(1,x6,x4),(2,x16,x1)] (by decide +kernel)
def p63 := prefixPool s0 [(1,x6,x4),(2,x16,x3)] (by decide +kernel)
def p64 := prefixPool s0 [(2,x0,x1),(1,x0,x3)] (by decide +kernel)
def p65 := prefixPool s0 [(2,x0,x3)] (by decide +kernel)
def p66 := prefixPool s0 [(2,x0,x3),(1,x17,x1)] (by decide +kernel)
def p67 := prefixPool s0 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p68 := prefixPool s0 [(2,x0,x3),(3,x0,x3),(1,x6,x4)] (by decide +kernel)
def p69 := prefixPool s0 [(2,x0,x4),(1,x0,x1)] (by decide +kernel)
def p70 := prefixPool s0 [(2,x0,x4),(3,x0,x4)] (by decide +kernel)
def p71 := prefixPool s0 [(2,x1,x3)] (by decide +kernel)
def p72 := prefixPool s0 [(2,x1,x3),(0,x1,x3)] (by decide +kernel)
def p73 := prefixPool s0 [(2,x1,x6),(2,x18,x4)] (by decide +kernel)
def p74 := prefixPool s0 [(2,x1,x4)] (by decide +kernel)
def p75 := prefixPool s0 [(2,x1,x4),(1,x6,x4)] (by decide +kernel)
def p76 := prefixPool s0 [(2,x1,x4),(1,x6,x4),(0,x16,x1)] (by decide +kernel)
def p77 := prefixPool s0 [(2,x1,x4),(3,x0,x1)] (by decide +kernel)
def p78 := prefixPool s0 [(2,x1,x4),(3,x0,x1),(1,x6,x4)] (by decide +kernel)
def p79 := prefixPool s0 [(2,x6,x4)] (by decide +kernel)
def p80 := prefixPool s0 [(2,x6,x4),(0,x0,x3),(3,x5,x1)] (by decide +kernel)
def p81 := prefixPool s0 [(3,x0,x1)] (by decide +kernel)
def p82 := prefixPool s0 [(3,x0,x1),(0,x0,x1)] (by decide +kernel)
def p83 := prefixPool s0 [(3,x0,x1),(1,x0,x1),(1,x1,x3)] (by decide +kernel)
def p84 := prefixPool s0 [(3,x0,x1),(2,x19,x4)] (by decide +kernel)
def p85 := prefixPool s0 [(3,x0,x1),(2,x19,x4),(1,x6,x4)] (by decide +kernel)
def p86 := prefixPool s0 [(3,x0,x3)] (by decide +kernel)
def p87 := prefixPool s0 [(3,x0,x6),(1,x20,x4)] (by decide +kernel)
def p88 := prefixPool s0 [(3,x1,x3)] (by decide +kernel)
def p89 := prefixPool s0 [(3,x1,x3),(1,x0,x3)] (by decide +kernel)
def p90 := prefixPool s0 [(3,x3,x6),(1,x21,x4)] (by decide +kernel)
def p91 := prefixPool s0 [(3,x3,x4),(1,x22,x6)] (by decide +kernel)
def p92 := prefixPool s1 [] (by decide +kernel)
def p93 := prefixPool s1 [(0,x1,x3)] (by decide +kernel)
def p94 := prefixPool s1 [(0,x1,x23)] (by decide +kernel)
def p95 := prefixPool s1 [(0,x1,x23),(1,x24,x0)] (by decide +kernel)
def p96 := prefixPool s1 [(0,x3,x23)] (by decide +kernel)
def p97 := prefixPool s1 [(0,x3,x23),(1,x25,x0)] (by decide +kernel)
def p98 := prefixPool s1 [(1,x0,x3)] (by decide +kernel)
def p99 := prefixPool s1 [(1,x0,x4)] (by decide +kernel)
def p100 := prefixPool s1 [(1,x3,x4)] (by decide +kernel)
def p101 := prefixPool s1 [(2,x1,x4)] (by decide +kernel)
def p102 := prefixPool s1 [(3,x0,x1)] (by decide +kernel)
def p103 := prefixPool s1 [(3,x0,x23)] (by decide +kernel)
def p104 := prefixPool s2 [] (by decide +kernel)
def p105 := prefixPool s2 [(1,x0,x3)] (by decide +kernel)
def p106 := prefixPool s2 [(1,x0,x6)] (by decide +kernel)
def p107 := prefixPool s2 [(1,x3,x6)] (by decide +kernel)
def p108 := prefixPool s2 [(3,x0,x1)] (by decide +kernel)
def p109 := prefixPool s2 [(3,x0,x3)] (by decide +kernel)
def p110 := prefixPool s2 [(3,x0,x23)] (by decide +kernel)
def p111 := prefixPool s3 [] (by decide +kernel)
def p112 := prefixPool s3 [(0,x3,x23)] (by decide +kernel)
def p113 := prefixPool s3 [(0,x3,x23),(0,x25,x4)] (by decide +kernel)
def p114 := prefixPool s3 [(0,x3,x23),(1,x3,x23)] (by decide +kernel)
def p115 := prefixPool s3 [(0,x3,x6)] (by decide +kernel)
def p116 := prefixPool s3 [(0,x3,x6),(1,x26,x4)] (by decide +kernel)
def p117 := prefixPool s3 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p118 := prefixPool s3 [(0,x3,x4)] (by decide +kernel)
def p119 := prefixPool s3 [(0,x3,x4),(1,x27,x23),(1,x3,x4)] (by decide +kernel)
def p120 := prefixPool s3 [(0,x3,x4),(1,x27,x6)] (by decide +kernel)
def p121 := prefixPool s3 [(0,x3,x4),(1,x27,x6),(1,x3,x4)] (by decide +kernel)
def p122 := prefixPool s3 [(0,x3,x4),(1,x3,x4)] (by decide +kernel)
def p123 := prefixPool s3 [(0,x3,x4),(3,x27,x6)] (by decide +kernel)
def p124 := prefixPool s3 [(0,x23,x6)] (by decide +kernel)
def p125 := prefixPool s3 [(0,x23,x6),(1,x28,x4)] (by decide +kernel)
def p126 := prefixPool s3 [(0,x23,x6),(1,x23,x6)] (by decide +kernel)
def p127 := prefixPool s3 [(0,x23,x4)] (by decide +kernel)
def p128 := prefixPool s3 [(0,x23,x4),(1,x29,x3),(1,x23,x4)] (by decide +kernel)
def p129 := prefixPool s3 [(0,x23,x4),(1,x29,x6)] (by decide +kernel)
def p130 := prefixPool s3 [(0,x23,x4),(1,x29,x6),(1,x23,x4)] (by decide +kernel)
def p131 := prefixPool s3 [(0,x23,x4),(3,x29,x6)] (by decide +kernel)
def p132 := prefixPool s3 [(0,x6,x4)] (by decide +kernel)
def p133 := prefixPool s3 [(0,x6,x4),(1,x10,x3),(1,x6,x4)] (by decide +kernel)
def p134 := prefixPool s3 [(0,x6,x4),(1,x10,x23),(1,x6,x4)] (by decide +kernel)
def p135 := prefixPool s3 [(0,x6,x4),(1,x6,x4)] (by decide +kernel)
def p136 := prefixPool s3 [(0,x6,x4),(3,x10,x3)] (by decide +kernel)
def p137 := prefixPool s3 [(1,x3,x23)] (by decide +kernel)
def p138 := prefixPool s3 [(1,x3,x23),(0,x3,x23),(1,x25,x4)] (by decide +kernel)
def p139 := prefixPool s3 [(1,x3,x23),(1,x30,x6)] (by decide +kernel)
def p140 := prefixPool s3 [(1,x3,x23),(3,x30,x6)] (by decide +kernel)
def p141 := prefixPool s3 [(1,x3,x6)] (by decide +kernel)
def p142 := prefixPool s3 [(1,x3,x6),(0,x3,x6),(1,x26,x4)] (by decide +kernel)
def p143 := prefixPool s3 [(1,x3,x6),(0,x15,x23)] (by decide +kernel)
def p144 := prefixPool s3 [(1,x3,x6),(0,x15,x4),(1,x6,x4)] (by decide +kernel)
def p145 := prefixPool s3 [(1,x3,x6),(1,x6,x4)] (by decide +kernel)
def p146 := prefixPool s3 [(1,x3,x6),(1,x15,x4)] (by decide +kernel)
def p147 := prefixPool s3 [(1,x3,x6),(2,x15,x23)] (by decide +kernel)
def p148 := prefixPool s3 [(1,x3,x6),(2,x15,x4)] (by decide +kernel)
def p149 := prefixPool s3 [(1,x3,x6),(3,x15,x4)] (by decide +kernel)
def p150 := prefixPool s3 [(1,x3,x4)] (by decide +kernel)
def p151 := prefixPool s3 [(1,x3,x4),(1,x6,x4)] (by decide +kernel)
def p152 := prefixPool s3 [(1,x23,x6)] (by decide +kernel)
def p153 := prefixPool s3 [(1,x23,x6),(0,x23,x6),(1,x28,x4)] (by decide +kernel)
def p154 := prefixPool s3 [(1,x23,x6),(2,x31,x3)] (by decide +kernel)
def p155 := prefixPool s3 [(1,x23,x6),(3,x31,x4)] (by decide +kernel)
def p156 := prefixPool s3 [(1,x23,x4)] (by decide +kernel)
def p157 := prefixPool s3 [(1,x6,x4)] (by decide +kernel)
def p158 := prefixPool s3 [(1,x6,x4),(0,x16,x3)] (by decide +kernel)
def p159 := prefixPool s3 [(1,x6,x4),(0,x16,x23)] (by decide +kernel)
def p160 := prefixPool s3 [(1,x6,x4),(2,x16,x3)] (by decide +kernel)
def p161 := prefixPool s3 [(1,x6,x4),(2,x16,x23)] (by decide +kernel)
def p162 := prefixPool s3 [(2,x3,x23)] (by decide +kernel)
def p163 := prefixPool s3 [(2,x3,x23),(1,x32,x6)] (by decide +kernel)
def p164 := prefixPool s3 [(2,x3,x23),(2,x32,x6)] (by decide +kernel)
def p165 := prefixPool s3 [(2,x3,x23),(3,x3,x23)] (by decide +kernel)
def p166 := prefixPool s3 [(2,x3,x6)] (by decide +kernel)
def p167 := prefixPool s3 [(2,x3,x6),(2,x33,x4)] (by decide +kernel)
def p168 := prefixPool s3 [(2,x3,x6),(3,x3,x6)] (by decide +kernel)
def p169 := prefixPool s3 [(2,x3,x4)] (by decide +kernel)
def p170 := prefixPool s3 [(2,x3,x4),(1,x34,x6)] (by decide +kernel)
def p171 := prefixPool s3 [(2,x3,x4),(3,x3,x4)] (by decide +kernel)
def p172 := prefixPool s3 [(2,x23,x6)] (by decide +kernel)
def p173 := prefixPool s3 [(2,x23,x4)] (by decide +kernel)
def p174 := prefixPool s3 [(2,x23,x4),(3,x23,x4)] (by decide +kernel)
def p175 := prefixPool s3 [(2,x6,x4)] (by decide +kernel)
def p176 := prefixPool s3 [(2,x6,x4),(1,x3,x6)] (by decide +kernel)
def p177 := prefixPool s3 [(2,x6,x4),(3,x6,x4)] (by decide +kernel)
def p178 := prefixPool s3 [(3,x3,x23)] (by decide +kernel)
def p179 := prefixPool s3 [(3,x3,x6)] (by decide +kernel)
def p180 := prefixPool s3 [(3,x3,x6),(1,x21,x23)] (by decide +kernel)
def p181 := prefixPool s3 [(3,x3,x6),(1,x21,x4)] (by decide +kernel)
def p182 := prefixPool s3 [(3,x3,x6),(1,x23,x6)] (by decide +kernel)
def p183 := prefixPool s3 [(3,x3,x6),(1,x6,x4)] (by decide +kernel)
def p184 := prefixPool s3 [(3,x3,x6),(2,x21,x4)] (by decide +kernel)
def p185 := prefixPool s3 [(3,x3,x4)] (by decide +kernel)
def p186 := prefixPool s3 [(3,x3,x4),(1,x22,x6)] (by decide +kernel)
def p187 := prefixPool s3 [(3,x23,x6)] (by decide +kernel)
def p188 := prefixPool s3 [(3,x23,x6),(1,x35,x3)] (by decide +kernel)
def p189 := prefixPool s3 [(3,x23,x4),(1,x36,x6)] (by decide +kernel)
def p190 := prefixPool s3 [(3,x23,x4),(3,x36,x3)] (by decide +kernel)
def p191 := prefixPool s3 [(3,x6,x4)] (by decide +kernel)
def p192 := prefixPool s4 [] (by decide +kernel)
def p193 := prefixPool s5 [] (by decide +kernel)
def p194 := prefixPool s5 [(1,x6,x4)] (by decide +kernel)
def p195 := prefixPool s5 [(2,x6,x4)] (by decide +kernel)
def p196 := prefixPool s6 [] (by decide +kernel)
def p197 := prefixPool s7 [] (by decide +kernel)
def p198 := prefixPool s8 [] (by decide +kernel)
def p199 := prefixPool s8 [(0,x0,x23)] (by decide +kernel)
def p200 := prefixPool s8 [(0,x0,x23),(1,x0,x23)] (by decide +kernel)
def p201 := prefixPool s8 [(0,x0,x6)] (by decide +kernel)
def p202 := prefixPool s8 [(0,x0,x6),(1,x37,x4)] (by decide +kernel)
def p203 := prefixPool s8 [(0,x0,x6),(1,x0,x6)] (by decide +kernel)
def p204 := prefixPool s8 [(0,x0,x6),(3,x37,x23)] (by decide +kernel)
def p205 := prefixPool s8 [(0,x0,x6),(3,x37,x4)] (by decide +kernel)
def p206 := prefixPool s8 [(0,x0,x4)] (by decide +kernel)
def p207 := prefixPool s8 [(0,x0,x4),(1,x7,x6)] (by decide +kernel)
def p208 := prefixPool s8 [(0,x0,x4),(1,x7,x6),(1,x0,x4)] (by decide +kernel)
def p209 := prefixPool s8 [(0,x0,x4),(1,x0,x4)] (by decide +kernel)
def p210 := prefixPool s8 [(0,x0,x4),(3,x7,x23)] (by decide +kernel)
def p211 := prefixPool s8 [(0,x0,x4),(3,x7,x6)] (by decide +kernel)
def p212 := prefixPool s8 [(0,x23,x6)] (by decide +kernel)
def p213 := prefixPool s8 [(0,x23,x6),(1,x28,x4)] (by decide +kernel)
def p214 := prefixPool s8 [(0,x23,x6),(1,x23,x6)] (by decide +kernel)
def p215 := prefixPool s8 [(0,x23,x4)] (by decide +kernel)
def p216 := prefixPool s8 [(0,x23,x4),(1,x29,x6)] (by decide +kernel)
def p217 := prefixPool s8 [(0,x23,x4),(3,x29,x6)] (by decide +kernel)
def p218 := prefixPool s8 [(0,x6,x4)] (by decide +kernel)
def p219 := prefixPool s8 [(0,x6,x4),(1,x10,x0),(1,x6,x4)] (by decide +kernel)
def p220 := prefixPool s8 [(0,x6,x4),(1,x6,x4)] (by decide +kernel)
def p221 := prefixPool s8 [(0,x6,x4),(3,x10,x0)] (by decide +kernel)
def p222 := prefixPool s8 [(1,x0,x23)] (by decide +kernel)
def p223 := prefixPool s8 [(1,x0,x23),(1,x0,x6)] (by decide +kernel)
def p224 := prefixPool s8 [(1,x0,x23),(1,x0,x4)] (by decide +kernel)
def p225 := prefixPool s8 [(1,x0,x23),(1,x38,x6)] (by decide +kernel)
def p226 := prefixPool s8 [(1,x0,x23),(1,x38,x4)] (by decide +kernel)
def p227 := prefixPool s8 [(1,x0,x23),(3,x38,x6)] (by decide +kernel)
def p228 := prefixPool s8 [(1,x0,x6)] (by decide +kernel)
def p229 := prefixPool s8 [(1,x0,x6),(0,x0,x6),(1,x37,x4)] (by decide +kernel)
def p230 := prefixPool s8 [(1,x0,x6),(1,x0,x4)] (by decide +kernel)
def p231 := prefixPool s8 [(1,x0,x6),(1,x6,x4)] (by decide +kernel)
def p232 := prefixPool s8 [(1,x0,x6),(1,x13,x4)] (by decide +kernel)
def p233 := prefixPool s8 [(1,x0,x6),(2,x13,x23)] (by decide +kernel)
def p234 := prefixPool s8 [(1,x0,x6),(2,x13,x4)] (by decide +kernel)
def p235 := prefixPool s8 [(1,x0,x6),(3,x13,x4)] (by decide +kernel)
def p236 := prefixPool s8 [(1,x0,x4)] (by decide +kernel)
def p237 := prefixPool s8 [(1,x0,x4),(1,x6,x4)] (by decide +kernel)
def p238 := prefixPool s8 [(1,x0,x4),(2,x39,x6)] (by decide +kernel)
def p239 := prefixPool s8 [(1,x23,x6)] (by decide +kernel)
def p240 := prefixPool s8 [(1,x23,x6),(1,x6,x4)] (by decide +kernel)
def p241 := prefixPool s8 [(1,x23,x6),(1,x31,x4)] (by decide +kernel)
def p242 := prefixPool s8 [(1,x23,x6),(2,x31,x0)] (by decide +kernel)
def p243 := prefixPool s8 [(1,x23,x6),(3,x31,x4)] (by decide +kernel)
def p244 := prefixPool s8 [(1,x23,x4)] (by decide +kernel)
def p245 := prefixPool s8 [(1,x6,x4)] (by decide +kernel)
def p246 := prefixPool s8 [(1,x6,x4),(0,x16,x23)] (by decide +kernel)
def p247 := prefixPool s8 [(1,x6,x4),(2,x16,x0)] (by decide +kernel)
def p248 := prefixPool s8 [(1,x6,x4),(2,x16,x23)] (by decide +kernel)
def p249 := prefixPool s8 [(2,x0,x23)] (by decide +kernel)
def p250 := prefixPool s8 [(2,x0,x23),(2,x40,x6)] (by decide +kernel)
def p251 := prefixPool s8 [(2,x0,x23),(3,x0,x23)] (by decide +kernel)
def p252 := prefixPool s8 [(2,x0,x6)] (by decide +kernel)
def p253 := prefixPool s8 [(2,x0,x6),(1,x0,x23)] (by decide +kernel)
def p254 := prefixPool s8 [(2,x0,x6),(2,x41,x4)] (by decide +kernel)
def p255 := prefixPool s8 [(2,x0,x4)] (by decide +kernel)
def p256 := prefixPool s8 [(2,x0,x4),(1,x42,x6)] (by decide +kernel)
def p257 := prefixPool s8 [(2,x0,x4),(3,x0,x4)] (by decide +kernel)
def p258 := prefixPool s8 [(2,x23,x6)] (by decide +kernel)
def p259 := prefixPool s8 [(2,x23,x4)] (by decide +kernel)
def p260 := prefixPool s8 [(2,x23,x4),(3,x23,x4)] (by decide +kernel)
def p261 := prefixPool s8 [(2,x6,x4)] (by decide +kernel)
def p262 := prefixPool s8 [(2,x6,x4),(1,x43,x0)] (by decide +kernel)
def p263 := prefixPool s8 [(2,x6,x4),(1,x0,x6)] (by decide +kernel)
def p264 := prefixPool s8 [(2,x6,x4),(3,x6,x4)] (by decide +kernel)
def p265 := prefixPool s8 [(3,x0,x23)] (by decide +kernel)
def p266 := prefixPool s8 [(3,x0,x23),(1,x44,x6)] (by decide +kernel)
def p267 := prefixPool s8 [(3,x0,x23),(1,x23,x6)] (by decide +kernel)
def p268 := prefixPool s8 [(3,x0,x6)] (by decide +kernel)
def p269 := prefixPool s8 [(3,x0,x6),(0,x20,x4),(1,x6,x4)] (by decide +kernel)
def p270 := prefixPool s8 [(3,x0,x6),(1,x6,x4)] (by decide +kernel)
def p271 := prefixPool s8 [(3,x0,x6),(2,x20,x4)] (by decide +kernel)
def p272 := prefixPool s8 [(3,x0,x4)] (by decide +kernel)
def p273 := prefixPool s8 [(3,x0,x4),(1,x45,x6)] (by decide +kernel)
def p274 := prefixPool s8 [(3,x0,x4),(1,x6,x4)] (by decide +kernel)
def p275 := prefixPool s8 [(3,x23,x6)] (by decide +kernel)
def p276 := prefixPool s8 [(3,x23,x6),(1,x6,x4)] (by decide +kernel)
def p277 := prefixPool s8 [(3,x23,x4),(1,x36,x6)] (by decide +kernel)
def p278 := prefixPool s8 [(3,x23,x4),(1,x6,x4)] (by decide +kernel)
def p279 := prefixPool s8 [(3,x23,x4),(3,x36,x0)] (by decide +kernel)
def p280 := prefixPool s8 [(3,x6,x4)] (by decide +kernel)
def p281 := prefixPool s9 [] (by decide +kernel)
def p282 := prefixPool s9 [(1,x0,x3)] (by decide +kernel)
def p283 := prefixPool s9 [(1,x6,x4)] (by decide +kernel)
def p284 := prefixPool s10 [] (by decide +kernel)
def p285 := prefixPool s10 [(0,x0,x3)] (by decide +kernel)
def p286 := prefixPool s10 [(0,x0,x3),(0,x6,x4)] (by decide +kernel)
def p287 := prefixPool s10 [(0,x0,x3),(1,x5,x6)] (by decide +kernel)
def p288 := prefixPool s10 [(0,x0,x3),(1,x5,x4)] (by decide +kernel)
def p289 := prefixPool s10 [(0,x0,x3),(3,x5,x6)] (by decide +kernel)
def p290 := prefixPool s10 [(0,x0,x3),(3,x5,x4)] (by decide +kernel)
def p291 := prefixPool s10 [(0,x0,x6)] (by decide +kernel)
def p292 := prefixPool s10 [(0,x0,x6),(1,x37,x3)] (by decide +kernel)
def p293 := prefixPool s10 [(0,x0,x6),(1,x0,x6)] (by decide +kernel)
def p294 := prefixPool s10 [(0,x0,x4)] (by decide +kernel)
def p295 := prefixPool s10 [(0,x0,x4),(3,x7,x3)] (by decide +kernel)
def p296 := prefixPool s10 [(0,x3,x6)] (by decide +kernel)
def p297 := prefixPool s10 [(0,x3,x6),(1,x26,x0)] (by decide +kernel)
def p298 := prefixPool s10 [(0,x3,x6),(1,x26,x4)] (by decide +kernel)
def p299 := prefixPool s10 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p300 := prefixPool s10 [(0,x3,x4)] (by decide +kernel)
def p301 := prefixPool s10 [(0,x3,x4),(1,x27,x0),(1,x3,x4)] (by decide +kernel)
def p302 := prefixPool s10 [(0,x3,x4),(1,x3,x4)] (by decide +kernel)
def p303 := prefixPool s10 [(0,x6,x4)] (by decide +kernel)
def p304 := prefixPool s10 [(0,x6,x4),(1,x10,x0),(1,x6,x4)] (by decide +kernel)
def p305 := prefixPool s10 [(0,x6,x4),(1,x10,x3)] (by decide +kernel)
def p306 := prefixPool s10 [(0,x6,x4),(1,x6,x4)] (by decide +kernel)
def p307 := prefixPool s10 [(1,x0,x3)] (by decide +kernel)
def p308 := prefixPool s10 [(1,x0,x3),(0,x12,x4)] (by decide +kernel)
def p309 := prefixPool s10 [(1,x0,x3),(1,x0,x6)] (by decide +kernel)
def p310 := prefixPool s10 [(1,x0,x3),(1,x0,x6),(1,x3,x6)] (by decide +kernel)
def p311 := prefixPool s10 [(1,x0,x3),(1,x0,x6),(1,x13,x4)] (by decide +kernel)
def p312 := prefixPool s10 [(1,x0,x3),(1,x3,x6)] (by decide +kernel)
def p313 := prefixPool s10 [(1,x0,x3),(1,x12,x6)] (by decide +kernel)
def p314 := prefixPool s10 [(1,x0,x3),(1,x12,x4)] (by decide +kernel)
def p315 := prefixPool s10 [(1,x0,x3),(1,x12,x4),(1,x6,x4)] (by decide +kernel)
def p316 := prefixPool s10 [(1,x0,x3),(1,x6,x4)] (by decide +kernel)
def p317 := prefixPool s10 [(1,x0,x3),(2,x12,x6)] (by decide +kernel)
def p318 := prefixPool s10 [(1,x0,x3),(2,x12,x6),(1,x12,x6)] (by decide +kernel)
def p319 := prefixPool s10 [(1,x0,x3),(2,x12,x4)] (by decide +kernel)
def p320 := prefixPool s10 [(1,x0,x3),(3,x12,x6)] (by decide +kernel)
def p321 := prefixPool s10 [(1,x0,x6)] (by decide +kernel)
def p322 := prefixPool s10 [(1,x0,x6),(1,x3,x6)] (by decide +kernel)
def p323 := prefixPool s10 [(1,x0,x6),(1,x6,x4)] (by decide +kernel)
def p324 := prefixPool s10 [(1,x0,x6),(1,x13,x4)] (by decide +kernel)
def p325 := prefixPool s10 [(1,x0,x6),(2,x13,x3)] (by decide +kernel)
def p326 := prefixPool s10 [(1,x0,x6),(2,x13,x4)] (by decide +kernel)
def p327 := prefixPool s10 [(1,x0,x6),(3,x13,x4)] (by decide +kernel)
def p328 := prefixPool s10 [(1,x0,x4)] (by decide +kernel)
def p329 := prefixPool s10 [(1,x0,x4),(1,x3,x4)] (by decide +kernel)
def p330 := prefixPool s10 [(1,x0,x4),(1,x6,x4)] (by decide +kernel)
def p331 := prefixPool s10 [(1,x0,x4),(2,x39,x6)] (by decide +kernel)
def p332 := prefixPool s10 [(1,x3,x6)] (by decide +kernel)
def p333 := prefixPool s10 [(1,x3,x6),(1,x3,x4),(1,x6,x4)] (by decide +kernel)
def p334 := prefixPool s10 [(1,x3,x6),(1,x6,x4)] (by decide +kernel)
def p335 := prefixPool s10 [(1,x3,x6),(1,x15,x4)] (by decide +kernel)
def p336 := prefixPool s10 [(1,x3,x6),(2,x15,x0)] (by decide +kernel)
def p337 := prefixPool s10 [(1,x3,x6),(2,x15,x4)] (by decide +kernel)
def p338 := prefixPool s10 [(1,x3,x4)] (by decide +kernel)
def p339 := prefixPool s10 [(1,x3,x4),(1,x6,x4)] (by decide +kernel)
def p340 := prefixPool s10 [(1,x6,x4)] (by decide +kernel)
def p341 := prefixPool s10 [(1,x6,x4),(0,x16,x3)] (by decide +kernel)
def p342 := prefixPool s10 [(1,x6,x4),(2,x16,x0)] (by decide +kernel)
def p343 := prefixPool s10 [(1,x6,x4),(2,x16,x3)] (by decide +kernel)
def p344 := prefixPool s10 [(2,x0,x3)] (by decide +kernel)
def p345 := prefixPool s10 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p346 := prefixPool s10 [(2,x0,x6)] (by decide +kernel)
def p347 := prefixPool s10 [(2,x0,x6),(1,x41,x3)] (by decide +kernel)
def p348 := prefixPool s10 [(2,x0,x4)] (by decide +kernel)
def p349 := prefixPool s10 [(2,x0,x4),(3,x0,x4)] (by decide +kernel)
def p350 := prefixPool s10 [(2,x3,x6)] (by decide +kernel)
def p351 := prefixPool s10 [(2,x3,x6),(1,x33,x0)] (by decide +kernel)
def p352 := prefixPool s10 [(2,x3,x4)] (by decide +kernel)
def p353 := prefixPool s10 [(2,x3,x4),(1,x34,x0)] (by decide +kernel)
def p354 := prefixPool s10 [(2,x3,x4),(1,x34,x6)] (by decide +kernel)
def p355 := prefixPool s10 [(2,x3,x4),(1,x0,x3)] (by decide +kernel)
def p356 := prefixPool s10 [(2,x3,x4),(3,x3,x4)] (by decide +kernel)
def p357 := prefixPool s10 [(2,x6,x4)] (by decide +kernel)
def p358 := prefixPool s10 [(2,x6,x4),(0,x0,x3)] (by decide +kernel)
def p359 := prefixPool s10 [(2,x6,x4),(3,x6,x4)] (by decide +kernel)
def p360 := prefixPool s10 [(3,x0,x3)] (by decide +kernel)
def p361 := prefixPool s10 [(3,x0,x3),(1,x46,x6)] (by decide +kernel)
def p362 := prefixPool s10 [(3,x0,x3),(1,x3,x6)] (by decide +kernel)
def p363 := prefixPool s10 [(3,x0,x3),(2,x46,x6)] (by decide +kernel)
def p364 := prefixPool s10 [(3,x0,x3),(2,x46,x4)] (by decide +kernel)
def p365 := prefixPool s10 [(3,x0,x6)] (by decide +kernel)
def p366 := prefixPool s10 [(3,x0,x6),(2,x20,x4)] (by decide +kernel)
def p367 := prefixPool s10 [(3,x0,x4)] (by decide +kernel)
def p368 := prefixPool s10 [(3,x0,x4),(1,x3,x4)] (by decide +kernel)
def p369 := prefixPool s10 [(3,x0,x4),(1,x6,x4)] (by decide +kernel)
def p370 := prefixPool s10 [(3,x3,x6)] (by decide +kernel)
def p371 := prefixPool s11 [] (by decide +kernel)
def p372 := prefixPool s11 [(0,x0,x3)] (by decide +kernel)
def p373 := prefixPool s11 [(0,x0,x3),(1,x5,x4)] (by decide +kernel)
def p374 := prefixPool s11 [(0,x0,x3),(3,x5,x23)] (by decide +kernel)
def p375 := prefixPool s11 [(0,x0,x3),(3,x5,x4)] (by decide +kernel)
def p376 := prefixPool s11 [(0,x0,x4)] (by decide +kernel)
def p377 := prefixPool s11 [(0,x0,x4),(1,x7,x3)] (by decide +kernel)
def p378 := prefixPool s11 [(0,x0,x4),(1,x0,x4)] (by decide +kernel)
def p379 := prefixPool s11 [(0,x0,x4),(3,x7,x3)] (by decide +kernel)
def p380 := prefixPool s11 [(0,x0,x4),(3,x7,x23)] (by decide +kernel)
def p381 := prefixPool s11 [(0,x3,x23)] (by decide +kernel)
def p382 := prefixPool s11 [(0,x3,x23),(1,x25,x0)] (by decide +kernel)
def p383 := prefixPool s11 [(0,x3,x4)] (by decide +kernel)
def p384 := prefixPool s11 [(0,x3,x4),(1,x27,x0)] (by decide +kernel)
def p385 := prefixPool s11 [(0,x3,x4),(1,x3,x4)] (by decide +kernel)
def p386 := prefixPool s11 [(0,x3,x4),(3,x27,x0)] (by decide +kernel)
def p387 := prefixPool s11 [(1,x0,x3)] (by decide +kernel)
def p388 := prefixPool s11 [(1,x0,x3),(1,x0,x23)] (by decide +kernel)
def p389 := prefixPool s11 [(1,x0,x3),(1,x0,x4)] (by decide +kernel)
def p390 := prefixPool s11 [(1,x0,x3),(1,x3,x4)] (by decide +kernel)
def p391 := prefixPool s11 [(1,x0,x3),(1,x12,x23)] (by decide +kernel)
def p392 := prefixPool s11 [(1,x0,x3),(1,x12,x4)] (by decide +kernel)
def p393 := prefixPool s11 [(1,x0,x3),(2,x12,x23)] (by decide +kernel)
def p394 := prefixPool s11 [(1,x0,x3),(2,x12,x4)] (by decide +kernel)
def p395 := prefixPool s11 [(1,x0,x3),(3,x12,x4)] (by decide +kernel)
def p396 := prefixPool s11 [(1,x0,x23)] (by decide +kernel)
def p397 := prefixPool s11 [(1,x0,x23),(1,x0,x3),(1,x12,x4)] (by decide +kernel)
def p398 := prefixPool s11 [(1,x0,x23),(1,x0,x4)] (by decide +kernel)
def p399 := prefixPool s11 [(1,x0,x23),(1,x38,x4)] (by decide +kernel)
def p400 := prefixPool s11 [(1,x0,x23),(3,x38,x4)] (by decide +kernel)
def p401 := prefixPool s11 [(1,x0,x4)] (by decide +kernel)
def p402 := prefixPool s11 [(1,x0,x4),(1,x3,x4)] (by decide +kernel)
def p403 := prefixPool s11 [(1,x0,x4),(2,x39,x3)] (by decide +kernel)
def p404 := prefixPool s11 [(1,x0,x4),(2,x39,x23)] (by decide +kernel)
def p405 := prefixPool s11 [(1,x3,x23)] (by decide +kernel)
def p406 := prefixPool s11 [(1,x3,x23),(3,x30,x4)] (by decide +kernel)
def p407 := prefixPool s11 [(1,x3,x4)] (by decide +kernel)
def p408 := prefixPool s11 [(1,x3,x4),(2,x47,x0)] (by decide +kernel)
def p409 := prefixPool s11 [(1,x3,x4),(2,x47,x23)] (by decide +kernel)
def p410 := prefixPool s11 [(2,x0,x3)] (by decide +kernel)
def p411 := prefixPool s11 [(2,x0,x3),(1,x17,x23)] (by decide +kernel)
def p412 := prefixPool s11 [(2,x0,x3),(1,x0,x23)] (by decide +kernel)
def p413 := prefixPool s11 [(2,x0,x3),(2,x17,x23)] (by decide +kernel)
def p414 := prefixPool s11 [(2,x0,x3),(2,x17,x4)] (by decide +kernel)
def p415 := prefixPool s11 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p416 := prefixPool s11 [(2,x0,x23),(2,x40,x4)] (by decide +kernel)
def p417 := prefixPool s11 [(2,x0,x4)] (by decide +kernel)
def p418 := prefixPool s11 [(2,x0,x4),(1,x42,x3)] (by decide +kernel)
def p419 := prefixPool s11 [(2,x0,x4),(1,x0,x3)] (by decide +kernel)
def p420 := prefixPool s11 [(2,x0,x4),(1,x0,x23)] (by decide +kernel)
def p421 := prefixPool s11 [(2,x0,x4),(3,x0,x4)] (by decide +kernel)
def p422 := prefixPool s11 [(2,x3,x23)] (by decide +kernel)
def p423 := prefixPool s11 [(2,x3,x23),(2,x32,x4)] (by decide +kernel)
def p424 := prefixPool s11 [(2,x3,x4)] (by decide +kernel)
def p425 := prefixPool s11 [(2,x3,x4),(1,x0,x3)] (by decide +kernel)
def p426 := prefixPool s11 [(2,x3,x4),(3,x3,x4)] (by decide +kernel)
def p427 := prefixPool s11 [(3,x0,x3)] (by decide +kernel)
def p428 := prefixPool s11 [(3,x0,x3),(2,x46,x23)] (by decide +kernel)
def p429 := prefixPool s11 [(3,x0,x23)] (by decide +kernel)
def p430 := prefixPool s11 [(3,x0,x23),(1,x44,x3)] (by decide +kernel)
def p431 := prefixPool s11 [(3,x0,x4)] (by decide +kernel)
def p432 := prefixPool s11 [(3,x0,x4),(1,x45,x3)] (by decide +kernel)
def p433 := prefixPool s11 [(3,x3,x23)] (by decide +kernel)
def p434 := prefixPool s11 [(3,x3,x4)] (by decide +kernel)
def p435 := prefixPool s11 [(3,x3,x4),(1,x22,x0)] (by decide +kernel)
def p436 := prefixPool s11 [(3,x3,x4),(1,x0,x4)] (by decide +kernel)
def p437 := prefixPool s11 [(3,x23,x4)] (by decide +kernel)
def p438 := prefixPool s12 [] (by decide +kernel)
def p439 := prefixPool s12 [(0,x0,x3)] (by decide +kernel)
def p440 := prefixPool s12 [(0,x0,x3),(1,x5,x6)] (by decide +kernel)
def p441 := prefixPool s12 [(0,x0,x3),(3,x5,x23)] (by decide +kernel)
def p442 := prefixPool s12 [(0,x0,x3),(3,x5,x6)] (by decide +kernel)
def p443 := prefixPool s12 [(0,x0,x6)] (by decide +kernel)
def p444 := prefixPool s12 [(0,x0,x6),(1,x37,x3)] (by decide +kernel)
def p445 := prefixPool s12 [(0,x0,x6),(1,x0,x6)] (by decide +kernel)
def p446 := prefixPool s12 [(0,x0,x6),(3,x37,x23)] (by decide +kernel)
def p447 := prefixPool s12 [(0,x3,x23),(1,x25,x0)] (by decide +kernel)
def p448 := prefixPool s12 [(0,x3,x6)] (by decide +kernel)
def p449 := prefixPool s12 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p450 := prefixPool s12 [(0,x23,x6)] (by decide +kernel)
def p451 := prefixPool s12 [(1,x0,x3)] (by decide +kernel)
def p452 := prefixPool s12 [(1,x0,x3),(1,x0,x23)] (by decide +kernel)
def p453 := prefixPool s12 [(1,x0,x3),(1,x0,x6)] (by decide +kernel)
def p454 := prefixPool s12 [(1,x0,x3),(1,x3,x6)] (by decide +kernel)
def p455 := prefixPool s12 [(1,x0,x3),(1,x12,x23)] (by decide +kernel)
def p456 := prefixPool s12 [(1,x0,x3),(1,x12,x6)] (by decide +kernel)
def p457 := prefixPool s12 [(1,x0,x3),(2,x12,x23)] (by decide +kernel)
def p458 := prefixPool s12 [(1,x0,x3),(2,x12,x6)] (by decide +kernel)
def p459 := prefixPool s12 [(1,x0,x23)] (by decide +kernel)
def p460 := prefixPool s12 [(1,x0,x23),(1,x0,x6)] (by decide +kernel)
def p461 := prefixPool s12 [(1,x0,x23),(1,x38,x6)] (by decide +kernel)
def p462 := prefixPool s12 [(1,x0,x6)] (by decide +kernel)
def p463 := prefixPool s12 [(1,x0,x6),(2,x13,x3)] (by decide +kernel)
def p464 := prefixPool s12 [(1,x0,x6),(2,x13,x23)] (by decide +kernel)
def p465 := prefixPool s12 [(1,x3,x23)] (by decide +kernel)
def p466 := prefixPool s12 [(1,x3,x6)] (by decide +kernel)
def p467 := prefixPool s12 [(1,x3,x6),(2,x15,x0)] (by decide +kernel)
def p468 := prefixPool s12 [(1,x3,x6),(2,x15,x23)] (by decide +kernel)
def p469 := prefixPool s12 [(1,x23,x6)] (by decide +kernel)
def p470 := prefixPool s12 [(2,x0,x3)] (by decide +kernel)
def p471 := prefixPool s12 [(2,x0,x3),(1,x17,x6)] (by decide +kernel)
def p472 := prefixPool s12 [(2,x0,x3),(2,x17,x6)] (by decide +kernel)
def p473 := prefixPool s12 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p474 := prefixPool s12 [(2,x0,x23),(2,x40,x6)] (by decide +kernel)
def p475 := prefixPool s12 [(2,x0,x6)] (by decide +kernel)
def p476 := prefixPool s12 [(2,x0,x6),(1,x0,x3)] (by decide +kernel)
def p477 := prefixPool s12 [(2,x0,x6),(1,x0,x23)] (by decide +kernel)
def p478 := prefixPool s12 [(2,x3,x23),(2,x32,x6)] (by decide +kernel)
def p479 := prefixPool s12 [(2,x3,x6)] (by decide +kernel)
def p480 := prefixPool s12 [(2,x3,x6),(3,x3,x6)] (by decide +kernel)
def p481 := prefixPool s12 [(3,x0,x3)] (by decide +kernel)
def p482 := prefixPool s12 [(3,x0,x3),(1,x46,x6)] (by decide +kernel)
def p483 := prefixPool s12 [(3,x0,x23)] (by decide +kernel)
def p484 := prefixPool s12 [(3,x0,x6)] (by decide +kernel)
def p485 := prefixPool s12 [(3,x0,x6),(1,x20,x3)] (by decide +kernel)
def p486 := prefixPool s12 [(3,x3,x23),(1,x48,x0)] (by decide +kernel)
def p487 := prefixPool s12 [(3,x3,x6)] (by decide +kernel)
def p488 := prefixPool s12 [(3,x3,x6),(1,x21,x23)] (by decide +kernel)
def p489 := prefixPool s12 [(3,x23,x6)] (by decide +kernel)
def p490 := prefixPool s13 [] (by decide +kernel)
def p491 := prefixPool s14 [] (by decide +kernel)
def p492 := prefixPool s14 [(0,x1,x23)] (by decide +kernel)
def p493 := prefixPool s14 [(2,x0,x4)] (by decide +kernel)
def p494 := prefixPool s14 [(3,x0,x4)] (by decide +kernel)
def p495 := prefixPool s15 [] (by decide +kernel)
def p496 := prefixPool s15 [(3,x0,x4)] (by decide +kernel)
def p497 := prefixPool s16 [] (by decide +kernel)
def p498 := prefixPool s17 [] (by decide +kernel)
def p499 := prefixPool s17 [(1,x0,x6)] (by decide +kernel)
def p500 := prefixPool s17 [(3,x0,x1)] (by decide +kernel)
def p501 := prefixPool s18 [] (by decide +kernel)
def p502 := prefixPool s18 [(0,x0,x1)] (by decide +kernel)
def p503 := prefixPool s18 [(0,x0,x1),(1,x2,x3)] (by decide +kernel)
def p504 := prefixPool s18 [(0,x0,x1),(1,x2,x4)] (by decide +kernel)
def p505 := prefixPool s18 [(0,x0,x1),(2,x2,x4)] (by decide +kernel)
def p506 := prefixPool s18 [(0,x0,x1),(3,x2,x4)] (by decide +kernel)
def p507 := prefixPool s18 [(0,x0,x3)] (by decide +kernel)
def p508 := prefixPool s18 [(0,x0,x3),(1,x5,x4)] (by decide +kernel)
def p509 := prefixPool s18 [(0,x0,x3),(2,x5,x4)] (by decide +kernel)
def p510 := prefixPool s18 [(0,x0,x3),(3,x5,x1)] (by decide +kernel)
def p511 := prefixPool s18 [(0,x0,x3),(3,x5,x4)] (by decide +kernel)
def p512 := prefixPool s18 [(0,x0,x4)] (by decide +kernel)
def p513 := prefixPool s18 [(0,x0,x4),(1,x7,x3)] (by decide +kernel)
def p514 := prefixPool s18 [(0,x0,x4),(1,x0,x4)] (by decide +kernel)
def p515 := prefixPool s18 [(0,x0,x4),(3,x7,x1)] (by decide +kernel)
def p516 := prefixPool s18 [(0,x0,x4),(3,x7,x3)] (by decide +kernel)
def p517 := prefixPool s18 [(0,x1,x3)] (by decide +kernel)
def p518 := prefixPool s18 [(0,x1,x3),(1,x8,x0)] (by decide +kernel)
def p519 := prefixPool s18 [(0,x1,x3),(1,x8,x4)] (by decide +kernel)
def p520 := prefixPool s18 [(0,x1,x3),(1,x1,x3)] (by decide +kernel)
def p521 := prefixPool s18 [(0,x1,x3),(3,x8,x4)] (by decide +kernel)
def p522 := prefixPool s18 [(0,x1,x4)] (by decide +kernel)
def p523 := prefixPool s18 [(0,x1,x4),(1,x0,x3)] (by decide +kernel)
def p524 := prefixPool s18 [(0,x1,x4),(1,x49,x0)] (by decide +kernel)
def p525 := prefixPool s18 [(0,x1,x4),(1,x49,x3)] (by decide +kernel)
def p526 := prefixPool s18 [(0,x1,x4),(3,x49,x0)] (by decide +kernel)
def p527 := prefixPool s18 [(0,x1,x4),(3,x49,x3)] (by decide +kernel)
def p528 := prefixPool s18 [(0,x3,x4)] (by decide +kernel)
def p529 := prefixPool s18 [(0,x3,x4),(1,x27,x0)] (by decide +kernel)
def p530 := prefixPool s18 [(0,x3,x4),(1,x3,x4)] (by decide +kernel)
def p531 := prefixPool s18 [(1,x0,x1)] (by decide +kernel)
def p532 := prefixPool s18 [(1,x0,x1),(1,x0,x3)] (by decide +kernel)
def p533 := prefixPool s18 [(1,x0,x1),(1,x0,x4)] (by decide +kernel)
def p534 := prefixPool s18 [(1,x0,x3)] (by decide +kernel)
def p535 := prefixPool s18 [(1,x0,x3),(0,x12,x1)] (by decide +kernel)
def p536 := prefixPool s18 [(1,x0,x3),(0,x12,x1),(1,x0,x1)] (by decide +kernel)
def p537 := prefixPool s18 [(1,x0,x3),(1,x0,x4)] (by decide +kernel)
def p538 := prefixPool s18 [(1,x0,x3),(1,x3,x4)] (by decide +kernel)
def p539 := prefixPool s18 [(1,x0,x3),(1,x12,x4)] (by decide +kernel)
def p540 := prefixPool s18 [(1,x0,x3),(2,x12,x4)] (by decide +kernel)
def p541 := prefixPool s18 [(1,x0,x3),(3,x12,x4)] (by decide +kernel)
def p542 := prefixPool s18 [(1,x0,x4)] (by decide +kernel)
def p543 := prefixPool s18 [(1,x0,x4),(0,x39,x1)] (by decide +kernel)
def p544 := prefixPool s18 [(1,x0,x4),(0,x39,x1),(1,x0,x1)] (by decide +kernel)
def p545 := prefixPool s18 [(1,x0,x4),(0,x39,x3)] (by decide +kernel)
def p546 := prefixPool s18 [(1,x0,x4),(1,x3,x4)] (by decide +kernel)
def p547 := prefixPool s18 [(1,x0,x4),(2,x39,x1)] (by decide +kernel)
def p548 := prefixPool s18 [(1,x0,x4),(2,x39,x3)] (by decide +kernel)
def p549 := prefixPool s18 [(1,x0,x4),(2,x39,x3),(1,x0,x3)] (by decide +kernel)
def p550 := prefixPool s18 [(1,x1,x3)] (by decide +kernel)
def p551 := prefixPool s18 [(1,x3,x4)] (by decide +kernel)
def p552 := prefixPool s18 [(1,x3,x4),(0,x47,x1)] (by decide +kernel)
def p553 := prefixPool s18 [(1,x3,x4),(2,x47,x0)] (by decide +kernel)
def p554 := prefixPool s18 [(2,x0,x3)] (by decide +kernel)
def p555 := prefixPool s18 [(2,x0,x3),(1,x17,x4)] (by decide +kernel)
def p556 := prefixPool s18 [(2,x0,x3),(2,x17,x4)] (by decide +kernel)
def p557 := prefixPool s18 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p558 := prefixPool s18 [(2,x0,x4)] (by decide +kernel)
def p559 := prefixPool s18 [(2,x0,x4),(1,x42,x3)] (by decide +kernel)
def p560 := prefixPool s18 [(2,x0,x4),(1,x0,x3)] (by decide +kernel)
def p561 := prefixPool s18 [(2,x0,x4),(3,x0,x4)] (by decide +kernel)
def p562 := prefixPool s18 [(2,x1,x3)] (by decide +kernel)
def p563 := prefixPool s18 [(2,x1,x3),(3,x0,x1)] (by decide +kernel)
def p564 := prefixPool s18 [(2,x1,x4)] (by decide +kernel)
def p565 := prefixPool s18 [(2,x1,x4),(1,x50,x0)] (by decide +kernel)
def p566 := prefixPool s18 [(2,x3,x4)] (by decide +kernel)
def p567 := prefixPool s18 [(2,x3,x4),(1,x34,x0)] (by decide +kernel)
def p568 := prefixPool s18 [(2,x3,x4),(1,x0,x3)] (by decide +kernel)
def p569 := prefixPool s18 [(2,x3,x4),(1,x3,x4)] (by decide +kernel)
def p570 := prefixPool s18 [(2,x3,x4),(3,x0,x1)] (by decide +kernel)
def p571 := prefixPool s18 [(2,x3,x4),(3,x3,x4)] (by decide +kernel)
def p572 := prefixPool s18 [(3,x0,x1)] (by decide +kernel)
def p573 := prefixPool s18 [(3,x0,x1),(2,x19,x3)] (by decide +kernel)
def p574 := prefixPool s18 [(3,x0,x1),(2,x19,x4)] (by decide +kernel)
def p575 := prefixPool s18 [(3,x0,x3)] (by decide +kernel)
def p576 := prefixPool s18 [(3,x0,x3),(1,x46,x4)] (by decide +kernel)
def p577 := prefixPool s18 [(3,x0,x3),(1,x3,x4)] (by decide +kernel)
def p578 := prefixPool s18 [(3,x0,x3),(3,x46,x4)] (by decide +kernel)
def p579 := prefixPool s18 [(3,x0,x4)] (by decide +kernel)
def p580 := prefixPool s18 [(3,x0,x4),(1,x3,x4)] (by decide +kernel)
def p581 := prefixPool s18 [(3,x3,x4)] (by decide +kernel)
def p582 := prefixPool s18 [(3,x3,x4),(1,x22,x0)] (by decide +kernel)
def p583 := prefixPool s18 [(3,x3,x4),(1,x22,x1)] (by decide +kernel)
def p584 := prefixPool s18 [(3,x3,x4),(1,x0,x4)] (by decide +kernel)
def p585 := prefixPool s18 [(3,x3,x4),(3,x0,x1)] (by decide +kernel)
def p586 := prefixPool s19 [] (by decide +kernel)
def p587 := prefixPool s19 [(0,x0,x1)] (by decide +kernel)
def p588 := prefixPool s19 [(0,x0,x1),(1,x2,x3)] (by decide +kernel)
def p589 := prefixPool s19 [(0,x0,x1),(1,x2,x6)] (by decide +kernel)
def p590 := prefixPool s19 [(0,x0,x1),(3,x2,x6)] (by decide +kernel)
def p591 := prefixPool s19 [(0,x0,x3)] (by decide +kernel)
def p592 := prefixPool s19 [(0,x0,x3),(1,x5,x6)] (by decide +kernel)
def p593 := prefixPool s19 [(0,x0,x3),(1,x0,x3)] (by decide +kernel)
def p594 := prefixPool s19 [(0,x0,x3),(3,x5,x1)] (by decide +kernel)
def p595 := prefixPool s19 [(0,x0,x3),(3,x5,x6)] (by decide +kernel)
def p596 := prefixPool s19 [(0,x0,x6)] (by decide +kernel)
def p597 := prefixPool s19 [(0,x0,x6),(1,x37,x3)] (by decide +kernel)
def p598 := prefixPool s19 [(0,x0,x6),(1,x0,x6)] (by decide +kernel)
def p599 := prefixPool s19 [(0,x0,x6),(3,x37,x1)] (by decide +kernel)
def p600 := prefixPool s19 [(0,x0,x6),(3,x37,x3)] (by decide +kernel)
def p601 := prefixPool s19 [(0,x1,x3)] (by decide +kernel)
def p602 := prefixPool s19 [(0,x1,x3),(1,x8,x0)] (by decide +kernel)
def p603 := prefixPool s19 [(0,x1,x3),(1,x8,x6)] (by decide +kernel)
def p604 := prefixPool s19 [(0,x1,x3),(3,x8,x6)] (by decide +kernel)
def p605 := prefixPool s19 [(0,x1,x6)] (by decide +kernel)
def p606 := prefixPool s19 [(0,x1,x6),(1,x0,x3)] (by decide +kernel)
def p607 := prefixPool s19 [(0,x1,x6),(1,x9,x0)] (by decide +kernel)
def p608 := prefixPool s19 [(0,x1,x6),(1,x9,x3)] (by decide +kernel)
def p609 := prefixPool s19 [(0,x3,x6)] (by decide +kernel)
def p610 := prefixPool s19 [(0,x3,x6),(1,x26,x0)] (by decide +kernel)
def p611 := prefixPool s19 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p612 := prefixPool s19 [(1,x0,x1)] (by decide +kernel)
def p613 := prefixPool s19 [(1,x0,x1),(1,x0,x3)] (by decide +kernel)
def p614 := prefixPool s19 [(1,x0,x3)] (by decide +kernel)
def p615 := prefixPool s19 [(1,x0,x3),(0,x12,x1)] (by decide +kernel)
def p616 := prefixPool s19 [(1,x0,x3),(0,x12,x1),(1,x0,x1)] (by decide +kernel)
def p617 := prefixPool s19 [(1,x0,x3),(1,x0,x6)] (by decide +kernel)
def p618 := prefixPool s19 [(1,x0,x3),(1,x12,x6)] (by decide +kernel)
def p619 := prefixPool s19 [(1,x0,x6)] (by decide +kernel)
def p620 := prefixPool s19 [(1,x0,x6),(0,x13,x1)] (by decide +kernel)
def p621 := prefixPool s19 [(1,x0,x6),(2,x13,x3)] (by decide +kernel)
def p622 := prefixPool s19 [(1,x1,x3)] (by decide +kernel)
def p623 := prefixPool s19 [(1,x3,x6)] (by decide +kernel)
def p624 := prefixPool s19 [(1,x3,x6),(0,x15,x1)] (by decide +kernel)
def p625 := prefixPool s19 [(1,x3,x6),(2,x15,x0)] (by decide +kernel)
def p626 := prefixPool s19 [(2,x0,x3)] (by decide +kernel)
def p627 := prefixPool s19 [(2,x0,x3),(1,x17,x6)] (by decide +kernel)
def p628 := prefixPool s19 [(2,x0,x3),(2,x17,x6)] (by decide +kernel)
def p629 := prefixPool s19 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p630 := prefixPool s19 [(2,x0,x6)] (by decide +kernel)
def p631 := prefixPool s19 [(2,x0,x6),(1,x41,x3)] (by decide +kernel)
def p632 := prefixPool s19 [(2,x0,x6),(1,x0,x3)] (by decide +kernel)
def p633 := prefixPool s19 [(2,x1,x3)] (by decide +kernel)
def p634 := prefixPool s19 [(2,x1,x3),(3,x0,x1)] (by decide +kernel)
def p635 := prefixPool s19 [(2,x1,x6)] (by decide +kernel)
def p636 := prefixPool s19 [(2,x3,x6)] (by decide +kernel)
def p637 := prefixPool s19 [(2,x3,x6),(1,x33,x0)] (by decide +kernel)
def p638 := prefixPool s19 [(3,x0,x1)] (by decide +kernel)
def p639 := prefixPool s19 [(3,x0,x1),(1,x1,x3)] (by decide +kernel)
def p640 := prefixPool s19 [(3,x0,x1),(1,x1,x6)] (by decide +kernel)
def p641 := prefixPool s19 [(3,x0,x1),(1,x3,x6)] (by decide +kernel)
def p642 := prefixPool s19 [(3,x0,x1),(2,x19,x3)] (by decide +kernel)
def p643 := prefixPool s19 [(3,x0,x3)] (by decide +kernel)
def p644 := prefixPool s19 [(3,x0,x3),(1,x46,x6)] (by decide +kernel)
def p645 := prefixPool s19 [(3,x0,x3),(1,x3,x6)] (by decide +kernel)
def p646 := prefixPool s19 [(3,x0,x3),(3,x46,x6)] (by decide +kernel)
def p647 := prefixPool s19 [(3,x0,x6)] (by decide +kernel)
def p648 := prefixPool s19 [(3,x0,x6),(1,x20,x3)] (by decide +kernel)
def p649 := prefixPool s19 [(3,x1,x6),(1,x0,x3),(0,x12,x1)] (by decide +kernel)
def p650 := prefixPool s19 [(3,x3,x6)] (by decide +kernel)
def p651 := prefixPool s19 [(3,x3,x6),(3,x0,x1)] (by decide +kernel)
def p652 := prefixPool s20 [] (by decide +kernel)
def p653 := prefixPool s20 [(0,x1,x23)] (by decide +kernel)
def p654 := prefixPool s21 [] (by decide +kernel)
def p655 := prefixPool s21 [(1,x0,x3)] (by decide +kernel)
def p656 := prefixPool s22 [] (by decide +kernel)
def p657 := prefixPool s22 [(1,x0,x3)] (by decide +kernel)
def p658 := prefixPool s24 [] (by decide +kernel)
def p659 := prefixPool s33 [] (by decide +kernel)
def p660 := prefixPool s36 [] (by decide +kernel)
def p661 := prefixPool s44 [] (by decide +kernel)
def p662 := prefixPool s47 [] (by decide +kernel)
def p663 := prefixPool s50 [] (by decide +kernel)
def p664 := prefixPool s53 [] (by decide +kernel)
def p665 := prefixPool s55 [] (by decide +kernel)
def p666 := prefixPool s56 [] (by decide +kernel)
def p667 := prefixPool s62 [] (by decide +kernel)
def p668 := prefixPool s66 [] (by decide +kernel)
def p669 := prefixPool s70 [] (by decide +kernel)
def p670 := prefixPool s74 [] (by decide +kernel)
def p671 := prefixPool s75 [] (by decide +kernel)
def p672 := prefixPool s79 [] (by decide +kernel)
def p673 := prefixPool s80 [] (by decide +kernel)
def p674 := prefixPool s86 [] (by decide +kernel)
def p675 := prefixPool s90 [] (by decide +kernel)
def p676 := prefixPool s94 [] (by decide +kernel)
def p677 := prefixPool s105 [] (by decide +kernel)
def cs : Array (ChosenPool R T) := #[
  usePool p0,
  usePool p1,
  usePool p2,
  usePool p3,
  usePool p4,
  usePool p5,
  usePool p6,
  usePool p7,
  usePool p8,
  usePool p9,
  usePool p10,
  usePool p11,
  usePool p12,
  usePool p14,
  usePool p15,
  usePool p16,
  usePool p18,
  usePool p19,
  usePool p20,
  usePool p21,
  usePool p22,
  usePool p23,
  usePool p24,
  usePool p25,
  usePool p26,
  usePool p27,
  usePool p28,
  usePool p29,
  usePool p32,
  usePool p33,
  usePool p34,
  usePool p35,
  usePool p36,
  usePool p37,
  usePool p38,
  usePool p39,
  usePool p40,
  usePool p41,
  usePool p42,
  usePool p43,
  usePool p44,
  usePool p45,
  usePool p46,
  usePool p48,
  usePool p49,
  usePool p50,
  usePool p51,
  usePool p52,
  usePool p53,
  usePool p54,
  usePool p55,
  usePool p56,
  usePool p57,
  usePool p58,
  usePool p59,
  usePool p60,
  usePool p61,
  usePool p62,
  usePool p63,
  usePool p64,
  usePool p65,
  usePool p66,
  usePool p67,
  usePool p68,
  usePool p69,
  usePool p70,
  usePool p71,
  usePool p73,
  usePool p74,
  usePool p75,
  usePool p76,
  usePool p77,
  usePool p78,
  usePool p79,
  usePool p81,
  usePool p84,
  usePool p85,
  usePool p86,
  usePool p87,
  usePool p88,
  usePool p89,
  usePool p90,
  usePool p91,
  usePool p92,
  usePool p98,
  usePool p99,
  usePool p100,
  usePool p101,
  usePool p102,
  usePool p103,
  usePool p104,
  usePool p105,
  usePool p106,
  usePool p107,
  usePool p108,
  usePool p109,
  usePool p110,
  usePool p111,
  usePool p112,
  usePool p113,
  usePool p114,
  usePool p115,
  usePool p116,
  usePool p117,
  usePool p118,
  usePool p119,
  usePool p120,
  usePool p121,
  usePool p122,
  usePool p123,
  usePool p124,
  usePool p125,
  usePool p126,
  usePool p127,
  usePool p128,
  usePool p129,
  usePool p130,
  usePool p131,
  usePool p132,
  usePool p133,
  usePool p134,
  usePool p135,
  usePool p136,
  usePool p137,
  usePool p138,
  usePool p139,
  usePool p140,
  usePool p141,
  usePool p142,
  usePool p143,
  usePool p144,
  usePool p145,
  usePool p146,
  usePool p147,
  usePool p148,
  usePool p149,
  usePool p150,
  usePool p151,
  usePool p152,
  usePool p153,
  usePool p154,
  usePool p155,
  usePool p156,
  usePool p157,
  usePool p158,
  usePool p159,
  usePool p160,
  usePool p161,
  usePool p162,
  usePool p163,
  usePool p164,
  usePool p165,
  usePool p166,
  usePool p167,
  usePool p168,
  usePool p169,
  usePool p170,
  usePool p171,
  usePool p172,
  usePool p173,
  usePool p174,
  usePool p175,
  usePool p176,
  usePool p177,
  usePool p178,
  usePool p179,
  usePool p180,
  usePool p181,
  usePool p182,
  usePool p183,
  usePool p184,
  usePool p185,
  usePool p186,
  usePool p187,
  usePool p188,
  usePool p189,
  usePool p190,
  usePool p191,
  usePool p192,
  usePool p193,
  usePool p194,
  usePool p195,
  usePool p196,
  usePool p197,
  usePool p198,
  usePool p199,
  usePool p200,
  usePool p201,
  usePool p202,
  usePool p203,
  usePool p204,
  usePool p205,
  usePool p206,
  usePool p207,
  usePool p208,
  usePool p209,
  usePool p210,
  usePool p211,
  usePool p212,
  usePool p213,
  usePool p214,
  usePool p215,
  usePool p216,
  usePool p217,
  usePool p218,
  usePool p219,
  usePool p220,
  usePool p221,
  usePool p222,
  usePool p223,
  usePool p224,
  usePool p225,
  usePool p226,
  usePool p227,
  usePool p228,
  usePool p229,
  usePool p230,
  usePool p231,
  usePool p232,
  usePool p233,
  usePool p234,
  usePool p235,
  usePool p236,
  usePool p237,
  usePool p238,
  usePool p239,
  usePool p240,
  usePool p241,
  usePool p242,
  usePool p243,
  usePool p244,
  usePool p245,
  usePool p246,
  usePool p247,
  usePool p248,
  usePool p249,
  usePool p250,
  usePool p251,
  usePool p252,
  usePool p253,
  usePool p254,
  usePool p255,
  usePool p256,
  usePool p257,
  usePool p258,
  usePool p259,
  usePool p260,
  usePool p261,
  usePool p262,
  usePool p263,
  usePool p264,
  usePool p265,
  usePool p266,
  usePool p267,
  usePool p268,
  usePool p269,
  usePool p270,
  usePool p271,
  usePool p272,
  usePool p273,
  usePool p274,
  usePool p275,
  usePool p276,
  usePool p277,
  usePool p278,
  usePool p279,
  usePool p280,
  usePool p281,
  usePool p283,
  usePool p284,
  joinPools p284 p10,
  joinPools p284 p81,
  usePool p285,
  joinPools p286 p7,
  usePool p287,
  usePool p288,
  usePool p289,
  usePool p290,
  usePool p291,
  usePool p292,
  usePool p293,
  usePool p294,
  usePool p295,
  usePool p296,
  usePool p297,
  usePool p298,
  usePool p299,
  usePool p300,
  usePool p301,
  usePool p302,
  usePool p303,
  usePool p304,
  usePool p305,
  usePool p306,
  usePool p307,
  joinPools p307 p14,
  joinPools p307 p29,
  usePool p308,
  usePool p309,
  joinPools p309 p30,
  joinPools p310 p31,
  joinPools p311 p282,
  usePool p312,
  usePool p313,
  joinPools p313 p518,
  joinPools p313 p535,
  usePool p314,
  joinPools p315 p616,
  joinPools p315 p649,
  joinPools p316 p523,
  joinPools p316 p606,
  usePool p317,
  joinPools p318 p536,
  usePool p319,
  usePool p320,
  usePool p321,
  usePool p322,
  joinPools p322 p13,
  joinPools p322 p83,
  usePool p323,
  usePool p324,
  joinPools p324 p524,
  joinPools p324 p607,
  joinPools p324 p620,
  usePool p325,
  usePool p326,
  usePool p327,
  usePool p328,
  usePool p329,
  usePool p330,
  usePool p331,
  usePool p332,
  joinPools p332 p17,
  joinPools p332 p47,
  joinPools p332 p517,
  joinPools p332 p572,
  usePool p333,
  usePool p334,
  joinPools p334 p520,
  usePool p335,
  joinPools p335 p624,
  joinPools p335 p641,
  usePool p336,
  usePool p337,
  joinPools p337 p570,
  usePool p338,
  joinPools p338 p16,
  joinPools p338 p601,
  usePool p339,
  joinPools p339 p639,
  joinPools p339 p640,
  usePool p340,
  joinPools p340 p522,
  joinPools p340 p572,
  joinPools p340 p605,
  usePool p341,
  usePool p342,
  usePool p343,
  joinPools p343 p585,
  joinPools p343 p651,
  usePool p344,
  joinPools p344 p72,
  usePool p345,
  usePool p346,
  usePool p347,
  usePool p348,
  usePool p349,
  usePool p350,
  usePool p351,
  usePool p352,
  usePool p353,
  usePool p354,
  usePool p355,
  usePool p356,
  usePool p357,
  joinPools p358 p80,
  usePool p359,
  usePool p360,
  joinPools p360 p82,
  usePool p361,
  usePool p362,
  usePool p363,
  usePool p364,
  usePool p365,
  usePool p366,
  usePool p367,
  usePool p368,
  usePool p369,
  usePool p370,
  usePool p371,
  usePool p372,
  usePool p373,
  usePool p374,
  usePool p375,
  usePool p376,
  usePool p377,
  usePool p378,
  usePool p379,
  usePool p380,
  usePool p381,
  usePool p382,
  usePool p383,
  usePool p384,
  usePool p385,
  usePool p386,
  usePool p387,
  usePool p388,
  usePool p389,
  usePool p390,
  usePool p391,
  usePool p392,
  joinPools p392 p94,
  usePool p393,
  usePool p394,
  usePool p395,
  usePool p396,
  joinPools p397 p95,
  usePool p398,
  usePool p399,
  usePool p400,
  usePool p401,
  usePool p402,
  usePool p403,
  joinPools p403 p93,
  usePool p404,
  usePool p405,
  usePool p406,
  usePool p407,
  usePool p408,
  joinPools p408 p94,
  usePool p409,
  usePool p410,
  usePool p411,
  usePool p412,
  usePool p413,
  usePool p414,
  usePool p415,
  usePool p416,
  usePool p417,
  usePool p418,
  usePool p419,
  usePool p420,
  usePool p421,
  usePool p422,
  usePool p423,
  usePool p424,
  usePool p425,
  usePool p426,
  usePool p427,
  usePool p428,
  usePool p429,
  usePool p430,
  usePool p431,
  usePool p432,
  usePool p433,
  usePool p434,
  usePool p435,
  usePool p436,
  usePool p437,
  usePool p438,
  usePool p439,
  usePool p440,
  usePool p441,
  usePool p442,
  usePool p443,
  usePool p444,
  usePool p445,
  usePool p446,
  usePool p447,
  usePool p448,
  usePool p449,
  usePool p450,
  usePool p451,
  usePool p452,
  usePool p453,
  usePool p454,
  usePool p455,
  usePool p456,
  usePool p457,
  usePool p458,
  usePool p459,
  usePool p460,
  usePool p461,
  usePool p462,
  usePool p463,
  usePool p464,
  usePool p465,
  usePool p466,
  usePool p467,
  usePool p468,
  usePool p469,
  usePool p470,
  usePool p471,
  usePool p472,
  usePool p473,
  usePool p474,
  usePool p475,
  usePool p476,
  usePool p477,
  usePool p478,
  usePool p479,
  usePool p480,
  usePool p481,
  usePool p482,
  usePool p483,
  usePool p484,
  usePool p485,
  usePool p486,
  usePool p487,
  usePool p488,
  usePool p489,
  usePool p490,
  usePool p491,
  joinPools p491 p498,
  usePool p492,
  joinPools p493 p496,
  joinPools p494 p194,
  usePool p495,
  usePool p497,
  joinPools p497 p193,
  joinPools p497 p495,
  usePool p498,
  usePool p499,
  usePool p500,
  usePool p501,
  usePool p502,
  usePool p503,
  usePool p504,
  usePool p505,
  usePool p506,
  usePool p507,
  usePool p508,
  usePool p509,
  usePool p510,
  usePool p511,
  usePool p512,
  usePool p513,
  usePool p514,
  usePool p515,
  usePool p516,
  usePool p517,
  usePool p518,
  usePool p519,
  usePool p520,
  usePool p521,
  usePool p522,
  usePool p524,
  usePool p525,
  usePool p526,
  usePool p527,
  usePool p528,
  usePool p529,
  usePool p530,
  usePool p531,
  usePool p532,
  usePool p533,
  usePool p534,
  usePool p535,
  usePool p536,
  usePool p537,
  usePool p538,
  usePool p539,
  usePool p540,
  usePool p541,
  usePool p542,
  usePool p543,
  usePool p544,
  usePool p545,
  usePool p546,
  usePool p547,
  usePool p548,
  joinPools p548 p96,
  joinPools p549 p97,
  usePool p550,
  usePool p551,
  usePool p552,
  usePool p553,
  usePool p554,
  usePool p555,
  usePool p556,
  usePool p557,
  usePool p558,
  usePool p559,
  usePool p560,
  usePool p561,
  usePool p562,
  usePool p563,
  usePool p564,
  usePool p565,
  usePool p566,
  usePool p567,
  usePool p568,
  usePool p569,
  usePool p571,
  usePool p572,
  usePool p573,
  usePool p574,
  usePool p575,
  usePool p576,
  usePool p577,
  usePool p578,
  usePool p579,
  usePool p580,
  usePool p581,
  usePool p582,
  usePool p583,
  usePool p584,
  usePool p586,
  usePool p587,
  usePool p588,
  usePool p589,
  usePool p590,
  usePool p591,
  usePool p592,
  usePool p593,
  usePool p594,
  usePool p595,
  usePool p596,
  usePool p597,
  usePool p598,
  usePool p599,
  usePool p600,
  usePool p601,
  usePool p602,
  usePool p603,
  usePool p604,
  usePool p608,
  usePool p609,
  usePool p610,
  usePool p611,
  usePool p612,
  usePool p613,
  usePool p614,
  usePool p615,
  usePool p617,
  usePool p618,
  usePool p619,
  usePool p621,
  usePool p622,
  usePool p623,
  usePool p625,
  usePool p626,
  usePool p627,
  usePool p628,
  usePool p629,
  usePool p630,
  usePool p631,
  usePool p632,
  usePool p633,
  usePool p634,
  usePool p635,
  usePool p636,
  usePool p637,
  usePool p638,
  usePool p642,
  usePool p643,
  usePool p644,
  usePool p645,
  usePool p646,
  usePool p647,
  usePool p648,
  usePool p650,
  usePool p652,
  usePool p653,
  usePool p654,
  usePool p655,
  usePool p656,
  usePool p657,
  usePool p658,
  usePool p659,
  usePool p660,
  usePool p661,
  usePool p662,
  usePool p663,
  usePool p664,
  usePool p665,
  usePool p666,
  usePool p667,
  usePool p668,
  usePool p669,
  usePool p670,
  usePool p671,
  usePool p672,
  usePool p673,
  usePool p674,
  usePool p675,
  usePool p676,
  usePool p677]
def rc {k : Nat} (ps : List Nat) (ns : List (Closed T (k-1))) :
    Nat → List (ChosenPool R T) × List (Closed T (k-1)) :=
  fun _ => (ps.filterMap (fun i => cs[i]?),ns)
def cc (k : Nat) (w : List (Observed (asRow Pos) (asRow Neg))) (ps : List Nat)
    (ns : List (Closed T (k-1))) (h : stateCheck k w (rc (k := k) ps ns) = true) : Closed T k :=
  closeState (raw := R) correctPairs k w (rc (k := k) ps ns) h
def n0 := cc 8 [w0,w1,w7,w3,w8,w4,w5] [123,294,526,609] [] (by decide +kernel)
def n1 := cc 8 [w0,w1,w7,w3,w4,w9,w5] [1,179,405,521] [] (by decide +kernel)
def n2 := cc 8 [w0,w1,w2,w3,w4,w10,w5] [83,90,127,214,303,405,459,526] [] (by decide +kernel)
def n3 := cc 8 [w11,w0,w1,w2,w3,w4,w5] [83,90,155,241,313,389,609] [] (by decide +kernel)
def n4 := cc 8 [w0,w1,w2,w7,w3,w4,w12,w5] [138,178,179,405,609] [] (by decide +kernel)
def n5 := cc 8 [w0,w1,w2,w7,w3,w4,w5,w13] [83,143,178,231,294,351,517,521,526,609,662] [] (by decide +kernel)
def v0 : Closed T 8 := rotateClosed n3 auto1 auto1ok
def v1 : Closed T 8 := rotateClosed n4 auto1 auto1ok
def v2 : Closed T 8 := rotateClosed n2 auto1 auto1ok
def v3 : Closed T 8 := rotateClosed n1 auto1 auto1ok
def n6 := cc 9 [w0,w1,w2,w7,w3,w4,w5] [0,97,178,179,184,294,405,472] [n3,v0,n4,v1,n5,n2,v2,n0,n1,v3] (by decide +kernel)
def n7 := cc 8 [w0,w1,w2,w3,w4,w14,w15] [2,136,222,664] [] (by decide +kernel)
def n8 := cc 8 [w17,w0,w1,w2,w3,w4,w5] [0,179,269,431,521] [] (by decide +kernel)
def n9 := cc 8 [w0,w1,w2,w3,w4,w14,w18] [90,142,179,269,527] [] (by decide +kernel)
def n10 := cc 8 [w0,w1,w2,w3,w4,w14,w13] [90,143,223,420,517,608,672] [] (by decide +kernel)
def n11 := cc 8 [w0,w1,w2,w3,w4,w5,w19] [83,90,143,179,184,320,420,483,527] [] (by decide +kernel)
def n12 := cc 8 [w20,w0,w1,w2,w3,w4,w5] [90,161,325,438,610,666] [] (by decide +kernel)
def v4 : Closed T 8 := rotateClosed n7 auto1 auto1ok
def v5 : Closed T 8 := rotateClosed n9 auto1 auto1ok
def v6 : Closed T 8 := rotateClosed n10 auto1 auto1ok
def n13 := cc 9 [w0,w1,w2,w3,w4,w16,w5] [97,214,315,389,459,525,666,671] [n12,n8,n2,n11,v4,v5,v6] (by decide +kernel)
def n14 := cc 8 [w21,w0,w1,w2,w3,w4,w5] [123,251,525,608] [] (by decide +kernel)
def n15 := cc 9 [w6,w0,w1,w2,w3,w8,w4,w5] [123,184,269,525,608] [n14,n0] (by decide +kernel)
def n16 := cc 8 [w22,w0,w1,w2,w3,w4,w5] [0,269,448,672] [] (by decide +kernel)
def n17 := cc 9 [w6,w0,w1,w2,w3,w4,w9,w5] [97,184,331,389,525,672] [n16,n2,v4,n1] (by decide +kernel)
def n18 := cc 8 [w23,w0,w1,w2,w3,w4,w5] [179,183,184,450,608] [] (by decide +kernel)
def n19 := cc 9 [w6,w0,w1,w2,w3,w4,w12,w5] [138,179,225,269,389,608] [n18,n4,v5] (by decide +kernel)
def n20 := cc 8 [w24,w0,w1,w2,w3,w4,w5] [143,184,356,529,611,662,671,672] [] (by decide +kernel)
def n21 := cc 9 [w6,w0,w1,w2,w3,w4,w5,w13] [83,143,231,351,389,459,525,608,662,671,672] [n20,n5,n11,n10,v6] (by decide +kernel)
def v7 : Closed T 9 := rotateClosed n17 auto1 auto1ok
def v8 : Closed T 9 := rotateClosed n19 auto1 auto1ok
def v9 : Closed T 9 := rotateClosed n13 auto1 auto1ok
def n22 := cc 10 [w6,w0,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n15,n17,v7,n19,v8,n21,n6,n13,v9] (by decide +kernel)
def n23 := cc 10 [w0,w1,w25,w2,w3,w4,w5] [97,184,269,389,459] [] (by decide +kernel)
def n24 := cc 9 [w0,w1,w2,w27,w4,w5] [0,97,184,389] [] (by decide +kernel)
def n25 := cc 9 [w0,w1,w28,w2,w4,w5] [97,184,269,389] [] (by decide +kernel)
def n26 := cc 10 [w26,w0,w1,w2,w3,w4,w5] [97,184,269,389,459] [n25,n24] (by decide +kernel)
def n27 := cc 8 [w30,w0,w31,w2,w3,w4,w5] [97,179,184,267,517] [] (by decide +kernel)
def n28 := cc 8 [w0,w1,w2,w3,w4,w32,w5] [83,90,152,238,311,459,595] [] (by decide +kernel)
def n29 := cc 8 [w33,w0,w1,w2,w3,w4,w5] [83,90,136,222,306,389,472,654] [] (by decide +kernel)
def n30 := cc 8 [w30,w0,w1,w2,w3,w4,w5,w13] [83,143,294,351,472,517,595,654,662] [] (by decide +kernel)
def v10 : Closed T 8 := rotateClosed n29 auto1 auto1ok
def v11 : Closed T 8 := rotateClosed n28 auto1 auto1ok
def n31 := cc 9 [w30,w0,w1,w2,w3,w4,w5] [0,97,184,267,294,389,472,517,521] [n29,v10,n27,n30,n28,v11] (by decide +kernel)
def n32 := cc 8 [w34,w0,w35,w2,w3,w4,w5] [97,267,664] [] (by decide +kernel)
def n33 := cc 8 [w0,w1,w2,w36,w3,w4,w5] [0,171,269,491,517] [] (by decide +kernel)
def n34 := cc 8 [w0,w1,w2,w3,w4,w37,w5] [83,177,179,224,330,496,596] [] (by decide +kernel)
def n35 := cc 8 [w38,w0,w1,w2,w3,w4,w5] [83,143,179,218,320,483,596] [] (by decide +kernel)
def n36 := cc 7 [w34,w0,w1,w2,w3,w9,w13] [45,76,93,131,223,420,512] [] (by decide +kernel)
def n37 := cc 8 [w34,w0,w1,w2,w3,w4,w9,w5] [43,75,83,127,222,327,331,512,664] [n36] (by decide +kernel)
def n38 := cc 8 [w34,w0,w1,w2,w3,w4,w13] [90,143,329,420,517,653] [n36] (by decide +kernel)
def n39 := cc 9 [w34,w0,w1,w2,w3,w4,w5] [97,222,327,389,459,653,664,670] [n35,n29,n32,n37,n38,n33,n34] (by decide +kernel)
def n40 := cc 8 [w40,w29,w0,w2,w3,w4,w5] [136,269,459,671] [] (by decide +kernel)
def n41 := cc 8 [w39,w29,w0,w2,w3,w4,w5,w13] [143,231,269,586,649,671,672] [] (by decide +kernel)
def v12 : Closed T 8 := rotateClosed n40 auto1 auto1ok
def n42 := cc 9 [w39,w29,w0,w2,w3,w4,w5] [97,184,267,269,389,459] [n40,v12,n41] (by decide +kernel)
def n43 := cc 8 [w29,w0,w2,w42,w3,w4,w5] [123,269,671,672] [] (by decide +kernel)
def n44 := cc 8 [w29,w0,w2,w3,w4,w43,w5] [138,179,269,389,676] [] (by decide +kernel)
def n45 := cc 7 [w29,w0,w41,w2,w3,w4,w15,w13] [137,184,268,349,350,389] [] (by decide +kernel)
def n46 := cc 6 [w29,w45,w41,w2,w3,w4,w5] [88,94,179] [] (by decide +kernel)
def n47 := cc 7 [w29,w0,w41,w2,w3,w4,w5,w44] [88,132,179,267,269,341] [n46] (by decide +kernel)
def n48 := cc 7 [w46,w29,w0,w41,w2,w3,w4,w5] [134,344,523] [] (by decide +kernel)
def v13 : Closed T 7 := rotateClosed n45 auto1 auto1ok
def n49 := cc 8 [w29,w0,w41,w2,w3,w4,w9,w5] [127,179,184,267,331,335,459,514,594,675] [n48,n47,v13] (by decide +kernel)
def n50 := cc 6 [w29,w0,w48,w2,w3,w4,w5] [] [] (by decide +kernel)
def n51 := cc 7 [w47,w29,w0,w41,w2,w3,w4,w5] [74,146,269,358,359] [n50] (by decide +kernel)
def n52 := cc 8 [w29,w0,w41,w2,w3,w4,w5,w13] [143,184,267,351,353,459,594,663,671,675] [n51,n47,n45,v13] (by decide +kernel)
def v14 : Closed T 8 := rotateClosed n49 auto1 auto1ok
def v15 : Closed T 8 := rotateClosed n44 auto1 auto1ok
def n53 := cc 9 [w29,w0,w41,w2,w3,w4,w5] [97,184,269,389,459] [n49,v14,n52,n43,n44,v15] (by decide +kernel)
def n54 := cc 8 [w50,w29,w0,w2,w3,w4,w5] [143,179,267,389,459] [] (by decide +kernel)
def n55 := cc 7 [w49,w29,w0,w2,w3,w9,w13] [72,131,231,487,662,672] [] (by decide +kernel)
def n56 := cc 8 [w49,w29,w0,w2,w3,w4,w9,w5] [71,127,179,184,331,389,487] [n55] (by decide +kernel)
def n57 := cc 8 [w49,w29,w0,w2,w3,w4,w13] [143,351,459,653,675] [n55] (by decide +kernel)
def n58 := cc 9 [w49,w29,w0,w2,w3,w4,w5] [97,184,269,389,459,653] [n54,n40,n56,n57] (by decide +kernel)
def n59 := cc 8 [w51,w0,w1,w2,w3,w4,w5] [123,267,594,653] [] (by decide +kernel)
def n60 := cc 9 [w29,w0,w1,w2,w3,w8,w4,w5] [123,184,271,594,653] [n59] (by decide +kernel)
def n61 := cc 8 [w52,w0,w1,w2,w3,w4,w5] [127,254,682] [] (by decide +kernel)
def v16 : Closed T 7 := rotateClosed n36 auto1 auto1ok
def v17 : Closed T 7 := rotateClosed n55 auto1 auto1ok
def n62 := cc 8 [w29,w0,w1,w2,w3,w4,w15,w13] [94,137,231,348,653,662,671,680] [v16,v17,n45] (by decide +kernel)
def n63 := cc 6 [w53,w45,w1,w2,w3,w4,w5] [83,90,179] [] (by decide +kernel)
def n64 := cc 7 [w29,w45,w1,w2,w3,w4,w5] [132,179,428,488] [n63,n46] (by decide +kernel)
def n65 := cc 8 [w29,w0,w1,w2,w3,w4,w5,w44] [46,132,179,267,339,427,487] [n64,n47] (by decide +kernel)
def n66 := cc 8 [w46,w29,w0,w1,w2,w3,w4,w5] [50,90,134,179,247,267,343,445,487,523] [n48] (by decide +kernel)
def v18 : Closed T 8 := rotateClosed n62 auto1 auto1ok
def n67 := cc 9 [w29,w0,w1,w2,w3,w4,w9,w5] [127,184,331,389,459,512,594,672] [v10,v12,n37,n56,n66,n61,n49,n65,v18] (by decide +kernel)
def n68 := cc 8 [w54,w0,w1,w2,w3,w4,w5] [138,179,184,267,450,653] [] (by decide +kernel)
def n69 := cc 8 [w55,w29,w0,w1,w2,w3,w4,w5] [140,267,454,653] [] (by decide +kernel)
def n70 := cc 9 [w29,w0,w1,w2,w3,w4,w12,w5] [138,184,267,271,389,653] [n69,n68] (by decide +kernel)
def n71 := cc 8 [w56,w0,w1,w2,w3,w4,w5] [143,179,184,267,452,505] [] (by decide +kernel)
def n72 := cc 8 [w47,w29,w0,w1,w2,w3,w4,w5] [58,146,179,267,357,455,508] [n51] (by decide +kernel)
def v19 : Closed T 8 := rotateClosed n38 auto1 auto1ok
def v20 : Closed T 8 := rotateClosed n57 auto1 auto1ok
def n73 := cc 9 [w29,w0,w1,w2,w3,w4,w5,w13] [143,231,351,389,459,594,653,675,684] [n35,n54,n38,v19,n57,v20,n30,n41,n72,n71,n52,n65,n62,v18] (by decide +kernel)
def v21 : Closed T 9 := rotateClosed n39 auto1 auto1ok
def v22 : Closed T 9 := rotateClosed n58 auto1 auto1ok
def v23 : Closed T 9 := rotateClosed n67 auto1 auto1ok
def v24 : Closed T 9 := rotateClosed n70 auto1 auto1ok
def n74 := cc 10 [w29,w0,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n39,v21,n58,v22,n31,n42,n53,n60,n67,v23,n70,v24,n73] (by decide +kernel)
def n75 := cc 9 [w0,w58,w2,w3,w4,w5] [97,184,269,389] [] (by decide +kernel)
def n76 := cc 7 [w59,w0,w2,w3,w4,w61] [111,199,273,390] [] (by decide +kernel)
def n77 := cc 7 [w63,w59,w0,w2,w3,w5] [117,203,375,390] [] (by decide +kernel)
def n78 := cc 6 [w64,w59,w0,w2,w4] [182,267,533,615] [] (by decide +kernel)
def v25 : Closed T 6 := rotateClosed n78 auto1 auto1ok
def n79 := cc 7 [w59,w0,w2,w60,w12,w5] [6,112,200,272] [v25] (by decide +kernel)
def v26 : Closed T 7 := rotateClosed n77 auto1 auto1ok
def n80 := cc 8 [w59,w0,w2,w60,w3,w4,w5] [198,272,675] [v26,n79,n76] (by decide +kernel)
def n81 := cc 8 [w59,w0,w2,w3,w4,w12,w5] [138,225,533,615] [n79] (by decide +kernel)
def n82 := cc 7 [w65,w66,w59,w0,w2,w4] [6,160,246,272] [n78] (by decide +kernel)
def n83 := cc 8 [w65,w59,w0,w2,w3,w4,w5] [159,245,272,615] [n82] (by decide +kernel)
def v27 : Closed T 7 := rotateClosed n82 auto1 auto1ok
def n84 := cc 8 [w67,w59,w0,w2,w3,w4,w5] [173,261,390,615] [v27] (by decide +kernel)
def n85 := cc 6 [w69,w59,w0,w2,w3] [512,533,669] [] (by decide +kernel)
def n86 := cc 7 [w59,w0,w2,w3,w68,w13] [7,206,675] [n85] (by decide +kernel)
def n87 := cc 8 [w59,w0,w2,w3,w68,w4,w5] [6,118,204,272,390,460] [n86] (by decide +kernel)
def n88 := cc 8 [w59,w0,w2,w3,w4,w5,w13] [231,272,533,615,675] [n86] (by decide +kernel)
def n89 := cc 7 [w70,w71,w59,w0,w2,w3] [163,250,390,460] [n85] (by decide +kernel)
def n90 := cc 8 [w70,w59,w0,w2,w3,w4,w5] [143,161,247,460,533] [n89] (by decide +kernel)
def v28 : Closed T 8 := rotateClosed n83 auto1 auto1ok
def v29 : Closed T 8 := rotateClosed n90 auto1 auto1ok
def v30 : Closed T 8 := rotateClosed n84 auto1 auto1ok
def v31 : Closed T 8 := rotateClosed n80 auto1 auto1ok
def v32 : Closed T 8 := rotateClosed n81 auto1 auto1ok
def n91 := cc 9 [w59,w0,w2,w3,w4,w5] [97,184] [n83,v28,n90,v29,n84,v30,n80,v31,n87,n81,v32,n88] (by decide +kernel)
def n92 := cc 9 [w0,w1,w2,w72,w4,w5] [97,184,524] [] (by decide +kernel)
def n93 := cc 6 [w69,w73,w0,w1,w2] [512,669,673] [] (by decide +kernel)
def n94 := cc 7 [w73,w0,w1,w2,w68,w13] [206,293,675] [n93] (by decide +kernel)
def n95 := cc 8 [w73,w0,w1,w2,w68,w4,w5] [118,204,290,392,462] [n94] (by decide +kernel)
def n96 := cc 8 [w73,w0,w1,w2,w4,w5,w13] [143,231,351,392,462] [n94] (by decide +kernel)
def n97 := cc 7 [w70,w71,w73,w0,w1,w2] [163,250,376,392,462] [n93] (by decide +kernel)
def n98 := cc 8 [w70,w73,w0,w1,w2,w4,w5] [143,161,247,374,392,462] [n97] (by decide +kernel)
def v33 : Closed T 8 := rotateClosed n98 auto1 auto1ok
def n99 := cc 9 [w73,w0,w1,w2,w4,w5] [97,184,269] [n98,v33,n95,n96] (by decide +kernel)
def n100 := cc 7 [w0,w1,w2,w3,w4,w75] [111,199,275,391] [] (by decide +kernel)
def n101 := cc 7 [w77,w0,w1,w2,w3,w5] [117,203,274,461] [] (by decide +kernel)
def n102 := cc 6 [w64,w0,w1,w2,w76] [182,274,511,613] [] (by decide +kernel)
def v34 : Closed T 6 := rotateClosed n102 auto1 auto1ok
def n103 := cc 7 [w0,w1,w2,w60,w12,w74] [5,112,200,275] [v34] (by decide +kernel)
def v35 : Closed T 7 := rotateClosed n101 auto1 auto1ok
def n104 := cc 8 [w0,w1,w2,w60,w3,w4,w74] [90,110,198,275,391,518] [v35,n103,n100] (by decide +kernel)
def n105 := cc 8 [w0,w1,w2,w3,w4,w12,w74] [225,531,674] [n103] (by decide +kernel)
def n106 := cc 7 [w65,w66,w0,w1,w2,w76] [4,160,246,274] [n102] (by decide +kernel)
def n107 := cc 8 [w65,w0,w1,w2,w3,w76,w5] [159,245,274,613] [n106] (by decide +kernel)
def v36 : Closed T 7 := rotateClosed n106 auto1 auto1ok
def n108 := cc 8 [w67,w0,w1,w2,w3,w4,w74] [5,173,261,391,664] [v36] (by decide +kernel)
def n109 := cc 7 [w0,w1,w2,w3,w76,w79] [111,274,512] [] (by decide +kernel)
def n110 := cc 7 [w81,w0,w1,w2,w3,w74] [117,203,275,391] [] (by decide +kernel)
def n111 := cc 6 [w83,w0,w1,w2,w4] [182,275,511,531] [] (by decide +kernel)
def v37 : Closed T 6 := rotateClosed n111 auto1 auto1ok
def n112 := cc 7 [w0,w1,w2,w78,w84,w5] [4,112,200,274] [v37] (by decide +kernel)
def v38 : Closed T 7 := rotateClosed n110 auto1 auto1ok
def n113 := cc 8 [w0,w1,w2,w78,w3,w76,w5] [198,274,675] [v38,n112,n109] (by decide +kernel)
def v39 : Closed T 7 := rotateClosed n112 auto1 auto1ok
def n114 := cc 8 [w0,w1,w2,w3,w4,w74,w82] [90,142,230,531] [v39] (by decide +kernel)
def n115 := cc 7 [w85,w86,w0,w1,w2,w4] [5,160,246,275] [n111] (by decide +kernel)
def n116 := cc 8 [w85,w0,w1,w2,w3,w4,w74] [159,245,275,664] [n115] (by decide +kernel)
def v40 : Closed T 7 := rotateClosed n115 auto1 auto1ok
def n117 := cc 8 [w87,w0,w1,w2,w3,w76,w5] [83,110,173,261,613] [v40] (by decide +kernel)
def n118 := cc 6 [w90,w0,w1,w2,w3] [512,613,669] [] (by decide +kernel)
def v41 : Closed T 6 := rotateClosed n118 auto1 auto1ok
def n119 := cc 7 [w0,w1,w2,w3,w91,w89] [90,121,206,531] [v41] (by decide +kernel)
def n120 := cc 8 [w0,w1,w2,w3,w91,w4,w74] [90,118,177,204,391,531] [n119] (by decide +kernel)
def n121 := cc 8 [w0,w1,w2,w3,w4,w74,w89] [143,231,275,531,664,674] [n119] (by decide +kernel)
def n122 := cc 7 [w92,w93,w0,w1,w2,w3] [163,391,518] [v41] (by decide +kernel)
def n123 := cc 8 [w92,w0,w1,w2,w3,w4,w74] [90,161,247,391,531] [n122] (by decide +kernel)
def v42 : Closed T 7 := rotateClosed n122 auto1 auto1ok
def n124 := cc 8 [w94,w0,w1,w2,w3,w76,w5] [83,161,274,512,613] [v42] (by decide +kernel)
def v43 : Closed T 8 := rotateClosed n107 auto1 auto1ok
def v44 : Closed T 8 := rotateClosed n124 auto1 auto1ok
def v45 : Closed T 8 := rotateClosed n117 auto1 auto1ok
def v46 : Closed T 8 := rotateClosed n113 auto1 auto1ok
def n125 := cc 9 [w0,w1,w2,w3,w4,w74] [97,184] [n116,n123,v43,v44,n108,v45,n104,v46,n120,n105,n114,n121] (by decide +kernel)
def n126 := cc 7 [w0,w1,w2,w3,w76,w61] [111,274,512] [] (by decide +kernel)
def n127 := cc 7 [w63,w0,w1,w2,w3,w74] [117,203,275,391] [] (by decide +kernel)
def v47 : Closed T 7 := rotateClosed n127 auto1 auto1ok
def n128 := cc 8 [w0,w1,w2,w60,w3,w76,w5] [198,530,675] [v47,n126] (by decide +kernel)
def n129 := cc 8 [w0,w1,w2,w3,w4,w74,w18] [90,142,230,269,531] [] (by decide +kernel)
def n130 := cc 8 [w65,w0,w1,w2,w3,w4,w74] [90,159,245,275,612] [] (by decide +kernel)
def n131 := cc 8 [w67,w0,w1,w2,w3,w76,w5] [83,110,173,261,269,613] [] (by decide +kernel)
def n132 := cc 6 [w95,w0,w1,w2,w3] [512,531,669] [] (by decide +kernel)
def n133 := cc 7 [w0,w1,w2,w3,w68,w89] [83,121,206,531] [n132] (by decide +kernel)
def n134 := cc 8 [w0,w1,w2,w3,w68,w4,w74] [90,118,177,204,391,531] [n133] (by decide +kernel)
def n135 := cc 8 [w0,w1,w2,w3,w4,w74,w13] [90,143,231,275,389,531,612] [] (by decide +kernel)
def n136 := cc 8 [w70,w0,w1,w2,w3,w76,w5] [83,118,161,247,390,459,461,530] [] (by decide +kernel)
def n137 := cc 7 [w70,w93,w0,w1,w2,w3] [83,163,531] [n132] (by decide +kernel)
def n138 := cc 8 [w70,w0,w1,w2,w3,w4,w74] [90,161,247,391,531] [n137] (by decide +kernel)
def n139 := cc 8 [w0,w1,w2,w3,w4,w5,w89] [83,143,161,231,269,531,613] [n133] (by decide +kernel)
def v48 : Closed T 7 := rotateClosed n137 auto1 auto1ok
def n140 := cc 8 [w94,w0,w1,w2,w3,w4,w5] [83,90,161,247,269,532,613] [v48] (by decide +kernel)
def v49 : Closed T 8 := rotateClosed n130 auto1 auto1ok
def v50 : Closed T 8 := rotateClosed n138 auto1 auto1ok
def v51 : Closed T 8 := rotateClosed n134 auto1 auto1ok
def v52 : Closed T 8 := rotateClosed n129 auto1 auto1ok
def v53 : Closed T 8 := rotateClosed n135 auto1 auto1ok
def n141 := cc 9 [w0,w1,w2,w3,w4,w76,w5] [97,184,269,459,530,666,675] [v49,v50,n136,n140,n131,n128,v51,n139,v52,v53] (by decide +kernel)
def n142 := cc 9 [w96,w0,w1,w2,w3,w5] [97,184,524] [] (by decide +kernel)
def n143 := cc 6 [w98,w0,w1,w2,w4] [182,277,511,531] [] (by decide +kernel)
def v54 : Closed T 6 := rotateClosed n143 auto1 auto1ok
def n144 := cc 7 [w0,w1,w2,w99,w12,w5] [112,182,200,613] [v54] (by decide +kernel)
def n145 := cc 8 [w0,w1,w2,w3,w99,w4,w5] [90,182,198,390,459] [n100,n144] (by decide +kernel)
def n146 := cc 7 [w101,w0,w1,w2,w3,w5] [115,202,276,463] [] (by decide +kernel)
def v55 : Closed T 7 := rotateClosed n146 auto1 auto1ok
def n147 := cc 8 [w57,w0,w1,w2,w3,w4,w61] [53,90,111,199,272,390,662] [n76,v55,n100,n126] (by decide +kernel)
def n148 := cc 7 [w102,w0,w1,w2,w3,w5] [117,203,274,461] [] (by decide +kernel)
def n149 := cc 8 [w63,w57,w0,w1,w2,w3,w5] [73,117,203,272,390,460] [n77,n127,n148] (by decide +kernel)
def n150 := cc 7 [w103,w0,w1,w2,w60,w5] [183,200,276] [v54] (by decide +kernel)
def n151 := cc 7 [w64,w57,w0,w1,w2,w4] [182,272,511,530,612] [n143,n78,n102] (by decide +kernel)
def v56 : Closed T 7 := rotateClosed n151 auto1 auto1ok
def n152 := cc 8 [w57,w0,w1,w2,w60,w12,w5] [112,200,272,612] [v56,n79,n150,n103,n144] (by decide +kernel)
def v57 : Closed T 8 := rotateClosed n149 auto1 auto1ok
def n153 := cc 9 [w57,w0,w1,w2,w60,w3,w4,w5] [198,272,389,607,675] [v57,n80,n152,n147,n104,n128,n145] (by decide +kernel)
def n154 := cc 8 [w103,w0,w1,w2,w3,w4,w5] [138,225,276,530,612] [n150] (by decide +kernel)
def n155 := cc 9 [w57,w0,w1,w2,w3,w4,w12,w5] [138,225,269,530,612] [n81,n154,n152,n105,v52] (by decide +kernel)
def n156 := cc 7 [w65,w104,w0,w1,w2,w4] [160,246,530,612] [] (by decide +kernel)
def n157 := cc 8 [w65,w66,w57,w0,w1,w2,w4] [160,246,272,530,607] [n82,n106,n156,n151] (by decide +kernel)
def n158 := cc 9 [w65,w57,w0,w1,w2,w3,w4,w5] [245,272,524,612,675] [n157,n83,n130,n107] (by decide +kernel)
def v58 : Closed T 7 := rotateClosed n156 auto1 auto1ok
def n159 := cc 8 [w105,w0,w1,w2,w3,w4,w5] [173,261,390,612] [v58] (by decide +kernel)
def v59 : Closed T 8 := rotateClosed n157 auto1 auto1ok
def n160 := cc 9 [w67,w57,w0,w1,w2,w3,w4,w5] [173,261,269,390,612] [v59,n84,n108,n131,n159] (by decide +kernel)
def n161 := cc 6 [w107,w0,w1,w2,w3] [393,515,534,662] [] (by decide +kernel)
def n162 := cc 7 [w0,w1,w2,w3,w106,w13] [121,512,530,662] [n161] (by decide +kernel)
def n163 := cc 8 [w0,w1,w2,w3,w4,w106,w5] [118,204,460,530] [n162] (by decide +kernel)
def n164 := cc 7 [w108,w0,w1,w2,w3,w68] [121,206,534,662] [n161] (by decide +kernel)
def n165 := cc 6 [w109,w0,w1,w2,w3] [512,531,669] [] (by decide +kernel)
def n166 := cc 7 [w69,w57,w0,w1,w2,w3] [389,512,530,662,664,669] [n161,n85,n93,n165] (by decide +kernel)
def n167 := cc 8 [w57,w0,w1,w2,w3,w68,w13] [206,389,530,675] [n166,n86,n94,n164,n133,n162] (by decide +kernel)
def n168 := cc 9 [w57,w0,w1,w2,w3,w68,w4,w5] [3,118,204,272,290,390,460,524] [n87,n95,n167,n134,v51,n163] (by decide +kernel)
def n169 := cc 8 [w108,w0,w1,w2,w3,w4,w5] [143,231,269,534,616,662] [n164] (by decide +kernel)
def n170 := cc 9 [w57,w0,w1,w2,w3,w4,w5,w13] [231,272,351,459,524,530,612,675] [n88,n96,n169,n167,n139,n135,v53] (by decide +kernel)
def n171 := cc 7 [w70,w110,w0,w1,w2,w3] [163,391,518] [n165] (by decide +kernel)
def v60 : Closed T 7 := rotateClosed n171 auto1 auto1ok
def n172 := cc 8 [w111,w0,w1,w2,w3,w4,w5] [143,161,461,512,530] [v60] (by decide +kernel)
def n173 := cc 8 [w70,w71,w57,w0,w1,w2,w3] [163,250,376,390,460,524] [n89,n97,n171,v60,n166] (by decide +kernel)
def n174 := cc 9 [w70,w57,w0,w1,w2,w3,w4,w5] [90,143,161,247,459,460,530] [n173,n90,n98,n138,n136,n172] (by decide +kernel)
def v61 : Closed T 9 := rotateClosed n158 auto1 auto1ok
def v62 : Closed T 9 := rotateClosed n174 auto1 auto1ok
def v63 : Closed T 9 := rotateClosed n160 auto1 auto1ok
def v64 : Closed T 9 := rotateClosed n142 auto1 auto1ok
def v65 : Closed T 9 := rotateClosed n153 auto1 auto1ok
def v66 : Closed T 9 := rotateClosed n155 auto1 auto1ok
def v67 : Closed T 9 := rotateClosed n141 auto1 auto1ok
def v68 : Closed T 9 := rotateClosed n125 auto1 auto1ok
def n175 := cc 10 [w57,w0,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n158,v61,n174,v62,n160,v63,n91,n99,n142,v64,n153,v65,n168,n155,v66,n170,n141,v67,n125,v68,n92,n75] (by decide +kernel)
def n176 := cc 8 [w113,w0,w1,w114,w3,w4,w5] [164,179,556,632] [] (by decide +kernel)
def n177 := cc 9 [w0,w1,w2,w114,w3,w112,w4,w5] [97,178,179,184,208,269,556,632] [n176] (by decide +kernel)
def n178 := cc 8 [w0,w1,w116,w114,w3,w4,w5] [179,294,517,521] [] (by decide +kernel)
def n179 := cc 8 [w0,w1,w2,w114,w3,w4,w117,w5] [138,187,671,674] [] (by decide +kernel)
def n180 := cc 8 [w115,w0,w1,w114,w3,w4,w9,w5] [183,302,556,672] [] (by decide +kernel)
def n181 := cc 8 [w118,w115,w0,w1,w114,w3,w4,w5] [251,372,672,674] [] (by decide +kernel)
def n182 := cc 8 [w115,w0,w1,w2,w3,w4,w119,w5] [303,556,672] [] (by decide +kernel)
def n183 := cc 8 [w120,w115,w0,w1,w2,w3,w4,w5] [178,313,672,674] [] (by decide +kernel)
def n184 := cc 8 [w115,w0,w1,w2,w114,w4,w12,w5] [138,178,179,253,294,556,632] [] (by decide +kernel)
def n185 := cc 8 [w115,w0,w1,w2,w114,w3,w4,w5,w13] [178,294,351,671,672,673,674] [] (by decide +kernel)
def v69 : Closed T 8 := rotateClosed n181 auto1 auto1ok
def v70 : Closed T 8 := rotateClosed n183 auto1 auto1ok
def v71 : Closed T 8 := rotateClosed n184 auto1 auto1ok
def v72 : Closed T 8 := rotateClosed n182 auto1 auto1ok
def v73 : Closed T 8 := rotateClosed n180 auto1 auto1ok
def v74 : Closed T 8 := rotateClosed n179 auto1 auto1ok
def n186 := cc 9 [w115,w0,w1,w2,w114,w3,w4,w5] [0,97,178,179,184,251,294,556,632] [n181,v69,n183,v70,n185,n184,v71,n182,v72,n180,v73,n179,v74,n178] (by decide +kernel)
def n187 := cc 8 [w0,w1,w114,w3,w4,w121,w15] [91,136,459,632,670,671] [] (by decide +kernel)
def n188 := cc 7 [w120,w122,w0,w1,w3,w4] [90,157,517] [] (by decide +kernel)
def v75 : Closed T 7 := rotateClosed n188 auto1 auto1ok
def n189 := cc 8 [w124,w0,w1,w114,w3,w4,w5] [165,517,521] [v75] (by decide +kernel)
def n190 := cc 8 [w120,w0,w1,w2,w3,w4,w121] [155,178,664] [n188] (by decide +kernel)
def n191 := cc 8 [w0,w1,w2,w3,w4,w119,w5] [30,83,90,127,214,303,405,459] [] (by decide +kernel)
def n192 := cc 8 [w0,w1,w2,w114,w3,w4,w121,w13] [143,178,329,517,632,672,675] [] (by decide +kernel)
def n193 := cc 8 [w0,w1,w2,w114,w3,w4,w5,w125] [143,184,294,320,559,671,672,675] [] (by decide +kernel)
def v76 : Closed T 8 := rotateClosed n190 auto1 auto1ok
def v77 : Closed T 8 := rotateClosed n192 auto1 auto1ok
def v78 : Closed T 8 := rotateClosed n187 auto1 auto1ok
def n194 := cc 9 [w0,w1,w2,w114,w3,w4,w123,w5] [97,184,294,315,389,483,556,671,672,675] [v76,n189,n193,v77,n191,v78] (by decide +kernel)
def n195 := cc 8 [w0,w1,w127,w114,w3,w4,w5] [127,405,521] [] (by decide +kernel)
def n196 := cc 8 [w0,w1,w2,w114,w3,w4,w129,w5] [83,84,143,184,472,521,632,662,671] [] (by decide +kernel)
def n197 := cc 8 [w126,w0,w1,w114,w3,w9,w5] [405,672] [] (by decide +kernel)
def n198 := cc 8 [w120,w128,w0,w1,w2,w3,w4] [155,178,521,632] [] (by decide +kernel)
def n199 := cc 8 [w126,w0,w1,w2,w114,w3,w5,w13] [143,178,517,521,556,662,665,670] [] (by decide +kernel)
def v79 : Closed T 8 := rotateClosed n198 auto1 auto1ok
def v80 : Closed T 8 := rotateClosed n196 auto1 auto1ok
def n200 := cc 9 [w126,w0,w1,w2,w114,w3,w4,w5] [97,184,472,505,517,556,675] [v79,n199,n197,v80,n191,n195] (by decide +kernel)
def n201 := cc 8 [w0,w1,w2,w3,w4,w130,w5] [83,90,127,214,303,405,459,557] [] (by decide +kernel)
def n202 := cc 8 [w131,w0,w1,w2,w3,w4,w5] [83,90,155,241,313,389,633] [] (by decide +kernel)
def n203 := cc 8 [w0,w31,w1,w2,w3,w4,w5,w13] [83,90,143,231,472,662,680] [] (by decide +kernel)
def v81 : Closed T 8 := rotateClosed n202 auto1 auto1ok
def v82 : Closed T 8 := rotateClosed n201 auto1 auto1ok
def n204 := cc 9 [w0,w31,w1,w2,w3,w4,w5] [0,97,184,294,389,472,680,682] [n202,v81,n27,n203,n201,v82] (by decide +kernel)
def n205 := cc 8 [w0,w1,w2,w114,w3,w4,w130,w5] [178,303,405,557,676] [] (by decide +kernel)
def n206 := cc 8 [w0,w31,w1,w114,w3,w4,w9,w5] [28,178,302,405,521] [] (by decide +kernel)
def n207 := cc 8 [w0,w31,w1,w2,w3,w4,w119,w5] [27,30,178,303,405,521] [] (by decide +kernel)
def n208 := cc 7 [w132,w0,w1,w2,w114,w3,w4,w5] [27,33] [] (by decide +kernel)
def n209 := cc 8 [w0,w31,w1,w2,w114,w3,w4,w12,w5] [27,178,179,267,294,296,405,676] [n208] (by decide +kernel)
def n210 := cc 7 [w133,w0,w1,w2,w114,w3,w4,w5] [132,146] [] (by decide +kernel)
def n211 := cc 6 [w31,w135,w2,w114,w3,w4,w5] [] [] (by decide +kernel)
def n212 := cc 7 [w0,w31,w134,w2,w114,w3,w4,w5] [143,179,675,676] [n211] (by decide +kernel)
def n213 := cc 8 [w0,w31,w1,w2,w114,w3,w4,w5,w13] [143,178,517,521,675,676] [n210,n212] (by decide +kernel)
def v83 : Closed T 8 := rotateClosed n209 auto1 auto1ok
def v84 : Closed T 8 := rotateClosed n207 auto1 auto1ok
def v85 : Closed T 8 := rotateClosed n206 auto1 auto1ok
def v86 : Closed T 8 := rotateClosed n205 auto1 auto1ok
def n214 := cc 9 [w0,w31,w1,w2,w114,w3,w4,w5] [26,97,178,267,294,405,472] [n27,n209,v83,n213,n207,v84,n206,v85,n205,v86] (by decide +kernel)
def n215 := cc 9 [w30,w0,w1,w2,w114,w3,w4,w5] [26,97,184,267,294,517,521] [n27] (by decide +kernel)
def n216 := cc 6 [w1,w136,w114,w3,w4,w137,w15] [182,208] [] (by decide +kernel)
def n217 := cc 6 [w139,w1,w136,w114,w3,w4,w5] [] [] (by decide +kernel)
def v87 : Closed T 6 := rotateClosed n216 auto1 auto1ok
def n218 := cc 7 [w1,w136,w2,w114,w3,w4,w138,w5] [211,314,315,406] [n217,v87] (by decide +kernel)
def n219 := cc 6 [w1,w136,w114,w3,w4,w15,w13] [] [] (by decide +kernel)
def n220 := cc 6 [w1,w136,w114,w3,w4,w5,w44] [182] [] (by decide +kernel)
def n221 := cc 6 [w46,w1,w136,w114,w3,w4,w5] [] [] (by decide +kernel)
def v88 : Closed T 6 := rotateClosed n219 auto1 auto1ok
def n222 := cc 7 [w1,w136,w114,w3,w4,w9,w5] [182,406,512,668] [n221,n220,v87,v88] (by decide +kernel)
def n223 := cc 6 [w140,w136,w2,w3,w4,w119,w5] [303,312,558] [] (by decide +kernel)
def n224 := cc 6 [w1,w136,w2,w3,w4,w141,w13] [307] [] (by decide +kernel)
def n225 := cc 6 [w1,w136,w2,w3,w4,w5,w142] [269,416] [] (by decide +kernel)
def n226 := cc 6 [w143,w1,w136,w2,w3,w4,w5] [] [] (by decide +kernel)
def v89 : Closed T 6 := rotateClosed n224 auto1 auto1ok
def n227 := cc 7 [w1,w136,w2,w3,w4,w119,w5] [267,303,512,554,668,669] [n226,n223,n225,v89] (by decide +kernel)
def n228 := cc 6 [w140,w136,w2,w114,w3,w4,w5] [303,312,558] [] (by decide +kernel)
def n229 := cc 7 [w1,w136,w2,w114,w3,w4,w119,w5] [21,165,213,294,668] [n228] (by decide +kernel)
def n230 := cc 6 [w1,w136,w2,w3,w4,w144,w5] [] [] (by decide +kernel)
def n231 := cc 7 [w120,w1,w136,w2,w3,w4,w5] [136,281,668] [n230] (by decide +kernel)
def n232 := cc 7 [w1,w136,w2,w114,w3,w4,w5,w13] [351,406,668] [n225,n224,v89,n220,n219,v88] (by decide +kernel)
def v90 : Closed T 7 := rotateClosed n231 auto1 auto1ok
def v91 : Closed T 7 := rotateClosed n218 auto1 auto1ok
def v92 : Closed T 7 := rotateClosed n229 auto1 auto1ok
def v93 : Closed T 7 := rotateClosed n227 auto1 auto1ok
def v94 : Closed T 7 := rotateClosed n222 auto1 auto1ok
def n233 := cc 8 [w1,w136,w2,w114,w3,w4,w5] [182,208,294,406,473,668] [n231,v90,n218,v91,n229,v92,n232,n227,v93,n222,v94] (by decide +kernel)
def n234 := cc 8 [w0,w1,w114,w42,w3,w4,w5] [179,294,517,521] [] (by decide +kernel)
def n235 := cc 8 [w0,w1,w2,w145,w3,w4,w5] [90,123,208,294,459,517] [] (by decide +kernel)
def n236 := cc 6 [w146,w0,w1,w3,w4,w15,w13] [178] [] (by decide +kernel)
def n237 := cc 6 [w146,w0,w1,w3,w4,w5,w44] [] [] (by decide +kernel)
def n238 := cc 6 [w46,w146,w0,w1,w3,w4,w5] [] [] (by decide +kernel)
def v95 : Closed T 6 := rotateClosed n236 auto1 auto1ok
def n239 := cc 7 [w146,w0,w1,w3,w4,w9,w5] [178,399,412] [n238,n237,v95] (by decide +kernel)
def n240 := cc 6 [w146,w0,w134,w2,w3,w4,w5] [301] [] (by decide +kernel)
def n241 := cc 7 [w146,w0,w1,w2,w3,w4,w5,w13] [33,83,90,235,294,412,662] [n240,n237,n236,v95] (by decide +kernel)
def v96 : Closed T 7 := rotateClosed n239 auto1 auto1ok
def n242 := cc 8 [w146,w0,w1,w2,w3,w4,w5] [83,90,178,294,412,478] [n241,n239,v96] (by decide +kernel)
def n243 := cc 8 [w0,w1,w2,w114,w3,w4,w43,w5] [178,179,225,294,405,676] [] (by decide +kernel)
def n244 := cc 6 [w147,w0,w1,w114,w3,w5,w13] [] [] (by decide +kernel)
def n245 := cc 7 [w147,w0,w1,w114,w3,w4,w5] [91,98,133,512] [n244] (by decide +kernel)
def n246 := cc 6 [w148,w0,w1,w114,w3,w4,w15] [178] [] (by decide +kernel)
def v97 : Closed T 6 := rotateClosed n244 auto1 auto1ok
def n247 := cc 7 [w0,w41,w1,w114,w3,w4,w15,w13] [180,408,668,676] [n236,v97,n246,n219] (by decide +kernel)
def n248 := cc 6 [w149,w0,w1,w114,w3,w4,w5] [97] [] (by decide +kernel)
def n249 := cc 7 [w0,w41,w1,w114,w3,w4,w5,w44] [84,91,132,179,408,475] [n237,n248,n220] (by decide +kernel)
def n250 := cc 7 [w46,w0,w41,w1,w114,w3,w4,w5] [91,134,446,521,667] [n238,n221] (by decide +kernel)
def v98 : Closed T 7 := rotateClosed n247 auto1 auto1ok
def n251 := cc 8 [w0,w41,w1,w114,w3,w4,w9,w5] [127,179,302,556,668,675,676,685] [n250,n239,n245,n249,v98,n222] (by decide +kernel)
def n252 := cc 6 [w150,w0,w1,w2,w3,w5,w13] [459] [] (by decide +kernel)
def n253 := cc 7 [w150,w0,w1,w2,w3,w4,w5] [10,79,90,126,133,174,412,459] [n252] (by decide +kernel)
def n254 := cc 7 [w150,w0,w1,w2,w3,w4,w119,w5] [83,129,179,512] [] (by decide +kernel)
def n255 := cc 7 [w0,w41,w140,w2,w3,w4,w119,w5] [83,179,303,557,668] [n223] (by decide +kernel)
def n256 := cc 6 [w148,w0,w1,w2,w3,w4,w141] [308] [] (by decide +kernel)
def v99 : Closed T 6 := rotateClosed n252 auto1 auto1ok
def n257 := cc 7 [w0,w41,w1,w2,w3,w4,w141,w13] [180,223,268,410,676] [v99,n256,n224] (by decide +kernel)
def n258 := cc 4 [w153,w0,w2,w4,w5] [] [] (by decide +kernel)
def n259 := cc 5 [w151,w0,w2,w152,w4,w5] [] [n258] (by decide +kernel)
def n260 := cc 6 [w151,w0,w1,w2,w3,w4,w5] [0,97] [n259] (by decide +kernel)
def n261 := cc 7 [w0,w41,w1,w2,w3,w4,w5,w142] [0,83,90,179,218,269,410,411,477] [n260,n225] (by decide +kernel)
def n262 := cc 7 [w143,w0,w41,w1,w2,w3,w4,w5] [83,90,134,220,413,521] [n226] (by decide +kernel)
def v100 : Closed T 7 := rotateClosed n257 auto1 auto1ok
def n263 := cc 8 [w0,w41,w1,w2,w3,w4,w119,w5] [83,127,179,214,267,303,477,556,668,669,675,678] [n262,n254,n253,n255,n261,v100,n227] (by decide +kernel)
def n264 := cc 7 [w150,w0,w1,w2,w114,w3,w4,w5] [27,33,126,174,213] [] (by decide +kernel)
def n265 := cc 7 [w0,w41,w140,w2,w114,w3,w4,w5] [26,179,305,668] [n228] (by decide +kernel)
def n266 := cc 8 [w0,w41,w1,w2,w114,w3,w4,w119,w5] [165,179,254,294,556,668,676] [n264,n265,n229] (by decide +kernel)
def n267 := cc 7 [w0,w41,w1,w2,w3,w4,w144,w5] [83,156,242,517,664] [n230] (by decide +kernel)
def n268 := cc 8 [w120,w0,w41,w1,w2,w3,w4,w5] [313,413,472,521,668,676] [n231,n267] (by decide +kernel)
def v101 : Closed T 6 := rotateClosed n256 auto1 auto1ok
def v102 : Closed T 6 := rotateClosed n246 auto1 auto1ok
def n269 := cc 7 [w148,w0,w1,w2,w114,w3,w4,w5] [57,178,179,351,458,510] [n256,v101,n246,v102] (by decide +kernel)
def n270 := cc 6 [w41,w135,w2,w114,w3,w4,w5] [301,546] [] (by decide +kernel)
def n271 := cc 7 [w0,w41,w134,w2,w114,w3,w4,w5] [26,54,309,310,351] [n240,n270] (by decide +kernel)
def n272 := cc 8 [w0,w41,w1,w2,w114,w3,w4,w5,w13] [26,53,231,294,351,405,517,668,675,676,684] [n241,n269,n271,n261,n257,v100,n249,n247,v98,n232] (by decide +kernel)
def v103 : Closed T 8 := rotateClosed n268 auto1 auto1ok
def v104 : Closed T 8 := rotateClosed n266 auto1 auto1ok
def v105 : Closed T 8 := rotateClosed n263 auto1 auto1ok
def v106 : Closed T 8 := rotateClosed n251 auto1 auto1ok
def v107 : Closed T 8 := rotateClosed n243 auto1 auto1ok
def n273 := cc 9 [w0,w41,w1,w2,w114,w3,w4,w5] [0,97,179,184,294,405,472,668] [n268,v103,n242,n266,v104,n272,n263,v105,n251,v106,n243,v107,n235,n234,n233] (by decide +kernel)
def n274 := cc 9 [w154,w0,w1,w2,w114,w3,w4,w5] [97,184,294,556,632] [] (by decide +kernel)
def n275 := cc 7 [w1,w156,w2,w114,w3,w5,w13] [217,474,517,556,662,669] [] (by decide +kernel)
def n276 := cc 8 [w1,w156,w2,w114,w3,w4,w5] [214,556,664,671] [n275] (by decide +kernel)
def n277 := cc 8 [w0,w1,w114,w157,w3,w4,w5] [16,127,405,521] [] (by decide +kernel)
def n278 := cc 8 [w0,w1,w2,w158,w3,w4,w5] [127,521,556] [] (by decide +kernel)
def n279 := cc 8 [w160,w0,w1,w2,w3,w4,w5] [178,472,521,632] [] (by decide +kernel)
def n280 := cc 8 [w0,w1,w2,w114,w3,w4,w161,w5] [84,143,178,521,632,662] [] (by decide +kernel)
def n281 := cc 8 [w120,w0,w159,w1,w2,w3,w4] [155,521,632,666] [] (by decide +kernel)
def n282 := cc 8 [w0,w155,w1,w2,w114,w3,w5,w13] [143,231,472,517,521,556,662,664] [n275] (by decide +kernel)
def v108 : Closed T 8 := rotateClosed n281 auto1 auto1ok
def v109 : Closed T 8 := rotateClosed n279 auto1 auto1ok
def v110 : Closed T 8 := rotateClosed n280 auto1 auto1ok
def n283 := cc 9 [w0,w155,w1,w2,w114,w3,w4,w5] [97,184,472,517,556,664] [v108,v109,n282,v110,n278,n277,n276] (by decide +kernel)
def n284 := cc 8 [w50,w0,w1,w2,w114,w3,w4,w5] [26,67,178,179,231,294,351,675] [] (by decide +kernel)
def n285 := cc 7 [w49,w0,w1,w114,w3,w9,w13] [29,521,668,675] [] (by decide +kernel)
def n286 := cc 8 [w49,w0,w1,w114,w3,w4,w9,w5] [28,127,302,405,521] [n285] (by decide +kernel)
def n287 := cc 7 [w49,w0,w1,w2,w3,w119,w13] [31,69,87,131,217,477] [] (by decide +kernel)
def n288 := cc 8 [w49,w0,w1,w2,w3,w4,w119,w5] [30,68,90,127,303,405,477,521] [n287] (by decide +kernel)
def n289 := cc 8 [w49,w162,w0,w1,w2,w3,w4,w5] [34,68,87,90,152,238,311,405,479,517,521] [] (by decide +kernel)
def n290 := cc 8 [w49,w120,w0,w1,w2,w3,w4] [155,241,664] [] (by decide +kernel)
def n291 := cc 8 [w49,w0,w1,w2,w114,w3,w4,w13] [231,351,472,521,632,668,675] [n287,n285] (by decide +kernel)
def n292 := cc 9 [w49,w0,w1,w2,w114,w3,w4,w5] [97,184,294,405,472,521,632,668] [n284,n29,n202,n290,n289,n291,n288,n286] (by decide +kernel)
def n293 := cc 8 [w163,w1,w2,w114,w3,w4,w5] [179,251,556] [] (by decide +kernel)
def n294 := cc 9 [w0,w1,w2,w114,w3,w8,w4,w5] [97,179,184,269,556,632] [n293] (by decide +kernel)
def n295 := cc 8 [w165,w1,w2,w114,w3,w4,w5] [179,208,294,517] [] (by decide +kernel)
def n296 := cc 9 [w164,w0,w1,w2,w114,w3,w4,w5] [0,97,179,184,294,517,521] [n295] (by decide +kernel)
def n297 := cc 8 [w166,w1,w114,w3,w4,w9,w5] [127,179,512,521] [] (by decide +kernel)
def n298 := cc 8 [w167,w1,w114,w3,w4,w9,w5] [521,678] [] (by decide +kernel)
def n299 := cc 8 [w0,w168,w1,w114,w3,w4,w9,w5] [179,521,685] [] (by decide +kernel)
def n300 := cc 8 [w0,w1,w169,w114,w3,w4,w9,w5] [178,302,521,556] [] (by decide +kernel)
def n301 := cc 7 [w0,w1,w114,w3,w9,w171] [178,180,405,556] [] (by decide +kernel)
def n302 := cc 8 [w0,w1,w170,w114,w3,w9,w5] [178,405,521] [n301] (by decide +kernel)
def n303 := cc 8 [w120,w0,w1,w114,w3,w4,w15] [459,517,668] [] (by decide +kernel)
def n304 := cc 8 [w0,w1,w114,w172,w3,w4,w9,w5] [179,302,512,521] [] (by decide +kernel)
def n305 := cc 8 [w65,w0,w1,w114,w3,w4,w9,w5] [302,556,672] [] (by decide +kernel)
def n306 := cc 7 [w0,w1,w173,w3,w4,w15] [517,668] [] (by decide +kernel)
def v111 : Closed T 7 := rotateClosed n285 auto1 auto1ok
def n307 := cc 8 [w0,w1,w114,w3,w4,w15,w13] [137,632,671,675] [v111,n247,n306] (by decide +kernel)
def n308 := cc 8 [w70,w0,w1,w114,w3,w9,w5] [405,521,671] [] (by decide +kernel)
def n309 := cc 8 [w0,w1,w114,w3,w4,w5,w44] [97,132,179,517,521,560] [n249] (by decide +kernel)
def n310 := cc 8 [w46,w0,w1,w114,w3,w4,w5] [134,591,672,675] [n250] (by decide +kernel)
def v112 : Closed T 8 := rotateClosed n303 auto1 auto1ok
def v113 : Closed T 8 := rotateClosed n307 auto1 auto1ok
def n311 := cc 9 [w0,w1,w114,w3,w4,w9,w5] [97,127,184,389,405,556,672,676] [n286,v112,n305,n308,n310,n180,n197,n298,n297,n206,n251,n299,n300,n302,n304,n309,v78,v113] (by decide +kernel)
def n312 := cc 8 [w167,w1,w2,w114,w3,w4,w5] [254,512,521] [] (by decide +kernel)
def n313 := cc 7 [w120,w174,w1,w2,w3,w4] [90,179,243,517] [] (by decide +kernel)
def n314 := cc 8 [w120,w0,w1,w2,w3,w4,w15] [178,241,517] [n313] (by decide +kernel)
def v114 : Closed T 8 := rotateClosed n314 auto1 auto1ok
def n315 := cc 9 [w0,w1,w2,w114,w3,w4,w9,w5] [83,97,179,184,294,331,389,521,556] [v114,n312,n191] (by decide +kernel)
def n316 := cc 8 [w0,w1,w176,w114,w3,w4,w5] [178,184,675] [] (by decide +kernel)
def n317 := cc 8 [w0,w1,w114,w3,w4,w177,w5] [184,591,672] [] (by decide +kernel)
def n318 := cc 8 [w0,w1,w114,w3,w4,w9,w5] [179,405,521] [] (by decide +kernel)
def n319 := cc 8 [w118,w178,w0,w1,w114,w3,w4,w5] [244,372,591,632,674] [] (by decide +kernel)
def v115 : Closed T 8 := rotateClosed n316 auto1 auto1ok
def v116 : Closed T 8 := rotateClosed n318 auto1 auto1ok
def n320 := cc 9 [w118,w0,w1,w114,w3,w4,w5] [97,178,184,521,632,675] [n319,n181,v115,n317,v116] (by decide +kernel)
def n321 := cc 8 [w180,w1,w2,w114,w3,w4,w5] [179,405,521] [] (by decide +kernel)
def n322 := cc 8 [w120,w181,w0,w1,w2,w3,w4] [178,472,517] [] (by decide +kernel)
def v117 : Closed T 8 := rotateClosed n322 auto1 auto1ok
def n323 := cc 9 [w179,w0,w1,w2,w114,w3,w4,w5] [97,179,184,405,521,556] [v117,n191,n318,n321] (by decide +kernel)
def n324 := cc 8 [w0,w1,w2,w114,w3,w4,w182,w5] [178,294,517,676] [] (by decide +kernel)
def n325 := cc 7 [w184,w0,w1,w2,w4,w5] [178,294,556,632] [] (by decide +kernel)
def n326 := cc 8 [w0,w1,w2,w169,w183,w4,w5] [100,186,294,360,377,556,632] [n325] (by decide +kernel)
def n327 := cc 8 [w0,w1,w2,w169,w3,w4,w119,w5] [178,303,521,556] [] (by decide +kernel)
def n328 := cc 7 [w185,w0,w1,w2,w114,w3,w4,w5] [26,132,146] [] (by decide +kernel)
def n329 := cc 8 [w0,w1,w2,w169,w114,w3,w4,w5,w13] [178,294,517,521,556,675,676] [n328] (by decide +kernel)
def v118 : Closed T 8 := rotateClosed n327 auto1 auto1ok
def v119 : Closed T 8 := rotateClosed n324 auto1 auto1ok
def v120 : Closed T 8 := rotateClosed n300 auto1 auto1ok
def n330 := cc 9 [w0,w1,w2,w169,w114,w3,w4,w5] [178,294,556,632] [n329,n327,v118,n326,n324,v119,n300,v120] (by decide +kernel)
def n331 := cc 8 [w0,w186,w1,w2,w114,w3,w4,w5] [179,294,556,632] [] (by decide +kernel)
def n332 := cc 9 [w0,w1,w2,w114,w3,w183,w4,w5] [179,267,294,556,632] [n176,n293,n331,n326] (by decide +kernel)
def n333 := cc 8 [w187,w188,w0,w1,w2,w4,w5] [60,77,151,237,294,556,632] [n325] (by decide +kernel)
def n334 := cc 9 [w187,w0,w1,w2,w114,w3,w4,w5] [269,556,632,668] [n333] (by decide +kernel)
def n335 := cc 9 [w188,w0,w1,w2,w114,w3,w4,w5] [0,179,294,517,521] [n333,n178,n295] (by decide +kernel)
def n336 := cc 8 [w120,w0,w1,w2,w3,w4,w5] [35,83,90,155,241,313,389] [] (by decide +kernel)
def n337 := cc 7 [w0,w1,w2,w3,w190,w141] [180,472,632] [] (by decide +kernel)
def v121 : Closed T 7 := rotateClosed n337 auto1 auto1ok
def n338 := cc 8 [w0,w1,w2,w114,w3,w4,w171] [178,405,517,556] [v121,n301] (by decide +kernel)
def n339 := cc 8 [w0,w1,w2,w114,w3,w4,w190,w5] [178,472,517,521,632] [] (by decide +kernel)
def n340 := cc 8 [w191,w0,w1,w2,w114,w3,w5] [109,197,405,472,556] [] (by decide +kernel)
def n341 := cc 7 [w192,w0,w1,w2,w3,w4] [178,472,517,632] [] (by decide +kernel)
def v122 : Closed T 7 := rotateClosed n341 auto1 auto1ok
def n342 := cc 8 [w0,w1,w2,w170,w3,w119,w5] [178,405,521] [v122,v121] (by decide +kernel)
def v123 : Closed T 8 := rotateClosed n336 auto1 auto1ok
def v124 : Closed T 8 := rotateClosed n340 auto1 auto1ok
def v125 : Closed T 8 := rotateClosed n339 auto1 auto1ok
def n343 := cc 9 [w0,w1,w2,w170,w114,w3,w4,w5] [97,178,184,405,472,517,556] [v123,v124,n342,v125,n338,n302] (by decide +kernel)
def n344 := cc 8 [w167,w0,w1,w2,w3,w4,w5] [0,269,448,672] [] (by decide +kernel)
def n345 := cc 7 [w124,w167,w1,w3,w4,w5] [83,179,436,580] [] (by decide +kernel)
def n346 := cc 8 [w167,w1,w2,w3,w4,w119,w5] [0,521,678] [n345] (by decide +kernel)
def n347 := cc 8 [w0,w140,w1,w2,w3,w4,w5] [127,214,682] [] (by decide +kernel)
def n348 := cc 8 [w0,w140,w1,w2,w3,w4,w119,w5] [83,127,303,521,557,668] [n255] (by decide +kernel)
def n349 := cc 8 [w124,w0,w1,w2,w3,w4,w5] [0,165,269,431,521] [] (by decide +kernel)
def n350 := cc 8 [w124,w0,w1,w3,w4,w119,w5] [0,521,669] [v75,n345] (by decide +kernel)
def n351 := cc 8 [w0,w1,w2,w193,w3,w4,w119,w5] [303,342,521,556] [] (by decide +kernel)
def n352 := cc 8 [w65,w0,w1,w2,w3,w4,w119,w5] [90,303,311,342,521,635] [] (by decide +kernel)
def n353 := cc 8 [w120,w0,w1,w2,w3,w4,w141] [0,517,668] [n188,n313] (by decide +kernel)
def v126 : Closed T 7 := rotateClosed n287 auto1 auto1ok
def n354 := cc 8 [w0,w1,w2,w3,w4,w141,w13] [90,137,389,632,671,680] [v126,n257] (by decide +kernel)
def n355 := cc 8 [w70,w0,w1,w2,w3,w119,w5] [405,448,517,521,556] [] (by decide +kernel)
def n356 := cc 7 [w0,w194,w2,w3,w4,w5] [83,179,267] [] (by decide +kernel)
def n357 := cc 8 [w0,w1,w2,w3,w4,w5,w142] [0,83,90,132,179,267,269,561] [n261,n356] (by decide +kernel)
def n358 := cc 8 [w143,w0,w1,w2,w3,w4,w5] [90,413,562,672] [n262] (by decide +kernel)
def v127 : Closed T 8 := rotateClosed n353 auto1 auto1ok
def v128 : Closed T 8 := rotateClosed n354 auto1 auto1ok
def n359 := cc 9 [w0,w1,w2,w3,w4,w119,w5] [83,127,214,269,405,459,556,672] [v10,n288,v123,v127,n352,n355,n358,n349,n350,n182,n344,n346,n263,n348,n347,n351,n357,v128] (by decide +kernel)
def n360 := cc 8 [w0,w140,w1,w2,w114,w3,w4,w5] [26,294,405,521,668] [n265] (by decide +kernel)
def n361 := cc 9 [w0,w1,w2,w114,w3,w4,w119,w5] [179,294,405,517,521,556] [v127,n189,n312,n207,n266,n360,n327,n342] (by decide +kernel)
def n362 := cc 8 [w0,w195,w1,w2,w3,w4,w5] [90,152,238,267,405,459] [] (by decide +kernel)
def n363 := cc 8 [w0,w1,w2,w3,w4,w144,w5] [156,562,664,672] [n267] (by decide +kernel)
def n364 := cc 8 [w196,w0,w1,w2,w3,w4,w5] [0,269,664,668] [] (by decide +kernel)
def n365 := cc 8 [w120,w178,w0,w1,w2,w3,w4,w5] [313,562,632,664] [] (by decide +kernel)
def v129 : Closed T 8 := rotateClosed n289 auto1 auto1ok
def v130 : Closed T 8 := rotateClosed n362 auto1 auto1ok
def v131 : Closed T 8 := rotateClosed n191 auto1 auto1ok
def n366 := cc 9 [w120,w0,w1,w2,w3,w4,w5] [97,155,184,241,269,389,521,632,675] [n364,n202,n290,v129,n365,n322,n183,n198,n268,n281,n190,n314,n353,v130,n363,v131] (by decide +kernel)
def n367 := cc 8 [w120,w197,w0,w1,w2,w3,w4] [178,472,517] [n341] (by decide +kernel)
def n368 := cc 8 [w120,w178,w0,w1,w2,w114,w3,w4,w5] [244,297,313,517,562] [] (by decide +kernel)
def n369 := cc 9 [w120,w0,w1,w2,w114,w3,w4,w5] [97,184,517,521,632,668] [n368,n367,n353,n303] (by decide +kernel)
def v132 : Closed T 8 := rotateClosed n367 auto1 auto1ok
def n370 := cc 9 [w198,w0,w1,w2,w114,w3,w4,w5] [179,405,521,556] [v132,n191,n195,n321] (by decide +kernel)
def n371 := cc 8 [w1,w2,w114,w3,w199,w4,w5] [294,671,675] [] (by decide +kernel)
def n372 := cc 8 [w0,w1,w114,w3,w200,w4,w5] [179,294,405,521] [] (by decide +kernel)
def n373 := cc 8 [w0,w1,w2,w3,w201,w4,w5] [90,179,294,405,459] [] (by decide +kernel)
def n374 := cc 8 [w202,w0,w1,w2,w3,w4,w5] [83,178,294,389,472] [] (by decide +kernel)
def n375 := cc 8 [w0,w1,w2,w114,w3,w4,w61] [294,662,671,675] [] (by decide +kernel)
def n376 := cc 8 [w0,w1,w2,w114,w3,w4,w100,w5] [294,521,662,676] [] (by decide +kernel)
def n377 := cc 8 [w63,w0,w1,w2,w114,w3,w5] [117,203,294,405,472] [] (by decide +kernel)
def n378 := cc 7 [w64,w0,w1,w2,w114,w4] [182,294,511,556,632] [] (by decide +kernel)
def v133 : Closed T 7 := rotateClosed n378 auto1 auto1ok
def n379 := cc 8 [w0,w1,w2,w114,w60,w12,w5] [112,200,294,632] [v133] (by decide +kernel)
def v134 : Closed T 8 := rotateClosed n374 auto1 auto1ok
def v135 : Closed T 8 := rotateClosed n377 auto1 auto1ok
def v136 : Closed T 8 := rotateClosed n376 auto1 auto1ok
def n380 := cc 9 [w0,w1,w2,w114,w60,w3,w4,w5] [97,184,294,632,671,675] [v134,v135,n379,v136,n375,n373,n372,n371] (by decide +kernel)
def n381 := cc 8 [w203,w0,w1,w2,w114,w3,w4,w5] [138,183,228,556,632] [] (by decide +kernel)
def n382 := cc 6 [w206,w1,w205,w114,w3,w4,w5] [] [] (by decide +kernel)
def n383 := cc 7 [w1,w205,w2,w114,w3,w4,w5] [138,211,267,299,406,631] [n382] (by decide +kernel)
def n384 := cc 6 [w1,w205,w114,w207,w3,w4,w5] [14,20,300] [] (by decide +kernel)
def n385 := cc 7 [w204,w1,w205,w2,w114,w3,w4,w5] [59,211,267] [n384] (by decide +kernel)
def n386 := cc 7 [w0,w204,w1,w114,w207,w3,w4,w5] [80,125,267] [n384] (by decide +kernel)
def n387 := cc 6 [w209,w0,w204,w1,w2,w3,w4] [] [] (by decide +kernel)
def n388 := cc 7 [w0,w204,w1,w2,w208,w3,w4,w5] [0,311,490] [n387] (by decide +kernel)
def n389 := cc 7 [w211,w0,w210,w1,w2,w3,w4,w5] [24,33] [] (by decide +kernel)
def v137 : Closed T 7 := rotateClosed n389 auto1 auto1ok
def n390 := cc 8 [w0,w204,w1,w2,w114,w3,w4,w5] [138,178,179,225,267,296,405,632] [v137,n388,n386,n385,n383] (by decide +kernel)
def n391 := cc 8 [w0,w1,w2,w212,w3,w4,w5] [97,178,267,556,632] [] (by decide +kernel)
def n392 := cc 8 [w213,w0,w1,w2,w3,w4,w5] [97,179,267,556,632] [] (by decide +kernel)
def n393 := cc 9 [w0,w1,w2,w114,w3,w4,w12,w5] [138,178,225,267,517,556,632] [n392,n184,n381,n209,n390,n391,n379] (by decide +kernel)
def n394 := cc 8 [w65,w66,w0,w1,w2,w114,w4] [160,246,294,556] [n378] (by decide +kernel)
def v138 : Closed T 8 := rotateClosed n319 auto1 auto1ok
def v139 : Closed T 8 := rotateClosed n368 auto1 auto1ok
def v140 : Closed T 8 := rotateClosed n365 auto1 auto1ok
def n395 := cc 9 [w65,w0,w1,w2,w114,w3,w4,w5] [245,294,521,632,675] [v138,v139,v140,n394,n352,n305] (by decide +kernel)
def n396 := cc 8 [w0,w1,w214,w114,w3,w4,w5] [179,405,632] [] (by decide +kernel)
def n397 := cc 8 [w0,w1,w2,w215,w3,w4,w5] [179,405,632] [] (by decide +kernel)
def n398 := cc 8 [w0,w1,w2,w216,w3,w4,w5] [176,265,472,556] [] (by decide +kernel)
def v141 : Closed T 8 := rotateClosed n394 auto1 auto1ok
def v142 : Closed T 8 := rotateClosed n398 auto1 auto1ok
def n399 := cc 9 [w67,w0,w1,w2,w114,w3,w4,w5] [184,405,632,671] [v141,v142,n397,n396] (by decide +kernel)
def n400 := cc 7 [w0,w1,w114,w3,w217,w13] [180,405,556,662] [] (by decide +kernel)
def n401 := cc 8 [w0,w1,w114,w3,w4,w217,w5] [179,292,405,472] [n400] (by decide +kernel)
def n402 := cc 7 [w0,w1,w2,w3,w218,w13] [180,405,556,662] [] (by decide +kernel)
def n403 := cc 8 [w0,w1,w2,w3,w4,w218,w5] [179,405,472,556] [n402] (by decide +kernel)
def n404 := cc 8 [w219,w0,w1,w2,w3,w4,w5] [122,207,405,472,556] [] (by decide +kernel)
def n405 := cc 7 [w69,w0,w1,w2,w114,w3] [405,556,662,671,675] [] (by decide +kernel)
def n406 := cc 7 [w69,w0,w1,w2,w114,w3,w13] [405,517,556,662,675] [] (by decide +kernel)
def n407 := cc 8 [w0,w1,w2,w114,w3,w68,w13] [405,556,662,671,675] [n405,n406,n402,n400] (by decide +kernel)
def n408 := cc 9 [w0,w1,w2,w114,w3,w68,w4,w5] [184,472,556,671] [n404,n407,n403,n401] (by decide +kernel)
def n409 := cc 8 [w220,w0,w1,w2,w114,w3,w4,w5] [26,56,143,184,294,356,672,675] [] (by decide +kernel)
def n410 := cc 6 [w221,w1,w135,w114,w3,w4,w5] [] [] (by decide +kernel)
def n411 := cc 7 [w1,w135,w2,w114,w3,w4,w5] [143,218,267,407,474] [n410,n211,n270] (by decide +kernel)
def n412 := cc 6 [w1,w135,w114,w222,w3,w4,w5] [267] [] (by decide +kernel)
def n413 := cc 7 [w134,w1,w135,w2,w114,w3,w4,w5] [218,267,675] [n412] (by decide +kernel)
def n414 := cc 7 [w0,w134,w1,w114,w222,w3,w4,w5] [132,153,267] [n412] (by decide +kernel)
def n415 := cc 7 [w0,w134,w1,w2,w223,w3,w4,w5] [54,83,351,413] [] (by decide +kernel)
def n416 := cc 7 [w224,w0,w134,w1,w2,w3,w4,w5] [83,132,143] [] (by decide +kernel)
def n417 := cc 8 [w0,w134,w1,w2,w114,w3,w4,w5] [26,143,178,179,231,267,294,351,405,459,675] [n416,n212,n271,n415,n414,n413,n411] (by decide +kernel)
def n418 := cc 7 [w1,w135,w2,w114,w3,w4,w5,w13] [407,662,675,676,680] [] (by decide +kernel)
def n419 := cc 7 [w224,w0,w1,w2,w3,w4,w5,w13] [410,413,477] [] (by decide +kernel)
def n420 := cc 8 [w0,w134,w1,w2,w114,w3,w4,w5,w13] [231,472,517,662,675,676,680] [n419,n418] (by decide +kernel)
def v143 : Closed T 7 := rotateClosed n306 auto1 auto1ok
def n421 := cc 8 [w0,w1,w2,w173,w3,w4,w5] [0,97,269,389,459,662,668] [n306,v143] (by decide +kernel)
def n422 := cc 8 [w0,w1,w2,w173,w114,w3,w4,w5,w13] [83,178,231,517,521] [] (by decide +kernel)
def n423 := cc 8 [w225,w0,w1,w2,w3,w4,w5] [0,179,269,684] [] (by decide +kernel)
def n424 := cc 7 [w1,w2,w114,w3,w227,w4,w5,w13] [351,634,662,675,676] [] (by decide +kernel)
def n425 := cc 7 [w228,w0,w1,w2,w3,w4,w5,w13] [410,477,562] [] (by decide +kernel)
def n426 := cc 8 [w0,w1,w2,w114,w226,w3,w4,w5,w13] [231,351,517,632,662,675,676] [n425,n424] (by decide +kernel)
def v144 : Closed T 8 := rotateClosed n291 auto1 auto1ok
def v145 : Closed T 8 := rotateClosed n199 auto1 auto1ok
def v146 : Closed T 8 := rotateClosed n282 auto1 auto1ok
def n427 := cc 9 [w0,w1,w2,w114,w3,w4,w5,w13] [143,178,184,231,294,351,389,459,521,556,632,662,671,675,676] [n284,n364,n291,v144,n30,n423,n185,n199,v145,n409,n213,n203,n272,n282,v146,n417,n420,n329,n422,n421,n426,n407,n193,n192,v77,n357,n354,v128,n309,n307,v113] (by decide +kernel)
def n428 := cc 8 [w0,w1,w229,w114,w3,w4,w5] [179,405,521] [] (by decide +kernel)
def n429 := cc 8 [w0,w1,w2,w230,w3,w4,w5] [179,405,521,556] [] (by decide +kernel)
def n430 := cc 8 [w0,w1,w2,w231,w3,w4,w5] [178,472,521,562] [] (by decide +kernel)
def n431 := cc 8 [w0,w1,w2,w114,w3,w4,w5,w13] [32,84,143,178,294,351,517,521,662] [] (by decide +kernel)
def n432 := cc 8 [w70,w71,w0,w1,w2,w114,w3] [163,250,405,472,556] [n405] (by decide +kernel)
def v147 : Closed T 8 := rotateClosed n430 auto1 auto1ok
def n433 := cc 9 [w70,w0,w1,w2,w114,w3,w4,w5] [184,405,472,556,671,675] [n432,n355,n308,v147,n431,n429,n428] (by decide +kernel)
def v148 : Closed T 9 := rotateClosed n292 auto1 auto1ok
def v149 : Closed T 9 := rotateClosed n320 auto1 auto1ok
def v150 : Closed T 9 := rotateClosed n369 auto1 auto1ok
def v151 : Closed T 9 := rotateClosed n366 auto1 auto1ok
def v152 : Closed T 9 := rotateClosed n395 auto1 auto1ok
def v153 : Closed T 9 := rotateClosed n433 auto1 auto1ok
def v154 : Closed T 9 := rotateClosed n399 auto1 auto1ok
def v155 : Closed T 9 := rotateClosed n370 auto1 auto1ok
def v156 : Closed T 9 := rotateClosed n323 auto1 auto1ok
def v157 : Closed T 9 := rotateClosed n200 auto1 auto1ok
def v158 : Closed T 9 := rotateClosed n283 auto1 auto1ok
def v159 : Closed T 9 := rotateClosed n343 auto1 auto1ok
def v160 : Closed T 9 := rotateClosed n380 auto1 auto1ok
def v161 : Closed T 9 := rotateClosed n194 auto1 auto1ok
def v162 : Closed T 9 := rotateClosed n315 auto1 auto1ok
def v163 : Closed T 9 := rotateClosed n361 auto1 auto1ok
def v164 : Closed T 9 := rotateClosed n393 auto1 auto1ok
def v165 : Closed T 9 := rotateClosed n359 auto1 auto1ok
def v166 : Closed T 9 := rotateClosed n311 auto1 auto1ok
def n434 := cc 10 [w0,w1,w2,w114,w3,w4,w5] [0,97,184,269,389,459] [n292,v148,n320,v149,n369,v150,n366,v151,n395,v152,n433,v153,n274,n334,n399,v154,n215,n31,n335,n370,v155,n296,n323,v156,n186,n200,v157,n214,n204,n273,n283,v158,n330,n343,v159,n380,v160,n177,n294,n332,n408,n194,v161,n315,v162,n361,v163,n393,v164,n427,n359,v165,n311,v166] (by decide +kernel)
def n435 := cc 9 [w0,w1,w2,w114,w3,w4,w5] [26,97,178,179,184,294,405,472] [n336,v123,n431,n191,v131,n318,v116] (by decide +kernel)
def n436 := cc 8 [w0,w1,w2,w3,w4,w233,w15] [90,136,184,517] [] (by decide +kernel)
def n437 := cc 8 [w179,w0,w1,w2,w3,w234,w5] [165,184,517,521] [] (by decide +kernel)
def n438 := cc 8 [w0,w1,w2,w3,w4,w233,w13] [90,143,223,389,517,521,578,641] [] (by decide +kernel)
def n439 := cc 8 [w70,w0,w1,w2,w3,w234,w5] [83,161,459,517,577] [] (by decide +kernel)
def n440 := cc 8 [w0,w1,w2,w3,w4,w5,w235] [0,83,90,143,218,269,517,521] [] (by decide +kernel)
def n441 := cc 8 [w236,w0,w1,w2,w3,w4,w5] [0,90,161,269,517] [] (by decide +kernel)
def v167 : Closed T 8 := rotateClosed n436 auto1 auto1ok
def v168 : Closed T 8 := rotateClosed n438 auto1 auto1ok
def n442 := cc 9 [w0,w1,w2,w3,w4,w234,w5] [97,214,269,459,517,577,666,675] [n439,n441,n437,n349,n191,n440,v167,v168] (by decide +kernel)
def n443 := cc 7 [w232,w237,w1,w3,w4,w61] [111,199,362,436] [] (by decide +kernel)
def n444 := cc 7 [w63,w232,w237,w1,w3,w5] [117,203,362,436] [] (by decide +kernel)
def n445 := cc 6 [w64,w232,w237,w1,w4] [182,362,511,580,644] [] (by decide +kernel)
def v169 : Closed T 6 := rotateClosed n445 auto1 auto1ok
def n446 := cc 7 [w232,w237,w1,w60,w12,w5] [62,112,200,362] [v169] (by decide +kernel)
def v170 : Closed T 7 := rotateClosed n444 auto1 auto1ok
def n447 := cc 8 [w232,w237,w1,w60,w3,w4,w5] [198,362,675] [v170,n446,n443] (by decide +kernel)
def n448 := cc 8 [w232,w237,w1,w3,w4,w12,w5] [138,225,580,644] [n446] (by decide +kernel)
def n449 := cc 7 [w65,w66,w232,w237,w1,w4] [62,160,246,362] [n445] (by decide +kernel)
def n450 := cc 8 [w65,w232,w237,w1,w3,w4,w5] [159,245,362,644] [n449] (by decide +kernel)
def v171 : Closed T 7 := rotateClosed n449 auto1 auto1ok
def n451 := cc 8 [w67,w232,w237,w1,w3,w4,w5] [173,261,436,644] [v171] (by decide +kernel)
def n452 := cc 6 [w69,w232,w237,w1,w3] [436,512,517,580] [] (by decide +kernel)
def n453 := cc 7 [w232,w237,w1,w3,w68,w13] [63,206,675] [n452] (by decide +kernel)
def n454 := cc 8 [w232,w237,w1,w3,w68,w4,w5] [62,118,204,362,436,494] [n453] (by decide +kernel)
def n455 := cc 8 [w232,w237,w1,w3,w4,w5,w13] [231,362,580,644,675] [n453] (by decide +kernel)
def n456 := cc 7 [w70,w71,w232,w237,w1,w3] [163,250,436,494] [n452] (by decide +kernel)
def n457 := cc 8 [w70,w232,w237,w1,w3,w4,w5] [143,161,247,436,494,580] [n456] (by decide +kernel)
def v172 : Closed T 8 := rotateClosed n450 auto1 auto1ok
def v173 : Closed T 8 := rotateClosed n457 auto1 auto1ok
def v174 : Closed T 8 := rotateClosed n451 auto1 auto1ok
def v175 : Closed T 8 := rotateClosed n447 auto1 auto1ok
def v176 : Closed T 8 := rotateClosed n448 auto1 auto1ok
def n458 := cc 9 [w232,w237,w1,w3,w4,w5] [97,184] [n450,v172,n457,v173,n451,v174,n447,v175,n454,n448,v176,n455] (by decide +kernel)
def n459 := cc 8 [w232,w163,w1,w2,w3,w4,w5] [3,123,251,362,577,641] [] (by decide +kernel)
def n460 := cc 9 [w232,w0,w1,w2,w3,w8,w4,w5] [123,184,269,577,641] [n459] (by decide +kernel)
def n461 := cc 8 [w232,w165,w1,w2,w3,w4,w5] [97,179,360,517] [] (by decide +kernel)
def n462 := cc 9 [w232,w164,w0,w1,w2,w3,w4,w5] [0,164,184,360,517,521] [n461] (by decide +kernel)
def n463 := cc 8 [w232,w167,w1,w2,w3,w4,w5] [127,512,521] [] (by decide +kernel)
def n464 := cc 9 [w232,w0,w1,w2,w3,w4,w9,w5] [83,97,179,184,331,360,389,521,577] [n463,n191,v167,n318] (by decide +kernel)
def n465 := cc 8 [w232,w180,w1,w2,w3,w4,w5] [97,179,431,521] [] (by decide +kernel)
def n466 := cc 9 [w232,w179,w0,w1,w2,w3,w4,w5] [165,184,521,577] [n465,n437,n349] (by decide +kernel)
def n467 := cc 8 [w0,w1,w2,w3,w238,w4,w5] [90,182,431,459,517] [] (by decide +kernel)
def n468 := cc 8 [w232,w1,w2,w3,w199,w4,w5] [110,182,517] [] (by decide +kernel)
def n469 := cc 8 [w232,w0,w1,w2,w3,w4,w61] [90,111,360,517,662] [n443] (by decide +kernel)
def n470 := cc 8 [w63,w232,w0,w1,w2,w3,w5] [117,203,294,360,431,491] [n444] (by decide +kernel)
def n471 := cc 7 [w64,w232,w0,w1,w2,w4] [26,182,360,511,577,641] [n445] (by decide +kernel)
def v177 : Closed T 7 := rotateClosed n471 auto1 auto1ok
def n472 := cc 8 [w232,w0,w1,w2,w60,w12,w5] [26,112,200,360,641] [v177,n446] (by decide +kernel)
def v178 : Closed T 8 := rotateClosed n470 auto1 auto1ok
def n473 := cc 9 [w232,w0,w1,w2,w60,w3,w4,w5] [97,360,517,675] [v178,n447,n472,n469,n468,n467] (by decide +kernel)
def n474 := cc 8 [w0,w1,w2,w239,w3,w4,w5] [26,138,183,577,641] [] (by decide +kernel)
def n475 := cc 9 [w232,w0,w1,w2,w3,w4,w12,w5] [26,138,179,225,269,577,641] [n448,n472,n474] (by decide +kernel)
def n476 := cc 8 [w65,w66,w232,w0,w1,w2,w4] [26,160,246,360,577] [n449,n471] (by decide +kernel)
def n477 := cc 9 [w65,w232,w0,w1,w2,w3,w4,w5] [245,294,360,641,675] [n476,n450] (by decide +kernel)
def n478 := cc 8 [w240,w0,w1,w2,w3,w4,w5] [26,183,431,641] [] (by decide +kernel)
def v179 : Closed T 8 := rotateClosed n476 auto1 auto1ok
def n479 := cc 9 [w67,w232,w0,w1,w2,w3,w4,w5] [26,173,179,261,431,641] [v179,n451,n478] (by decide +kernel)
def n480 := cc 7 [w0,w1,w2,w3,w241,w13] [121,517,577,662] [] (by decide +kernel)
def n481 := cc 8 [w0,w1,w2,w3,w4,w241,w5] [118,491,517,577] [n480] (by decide +kernel)
def n482 := cc 7 [w69,w232,w0,w1,w2,w3] [517,577,662,664,669] [n452] (by decide +kernel)
def n483 := cc 8 [w232,w0,w1,w2,w3,w68,w13] [431,517,577,675] [n482,n453,n480] (by decide +kernel)
def n484 := cc 9 [w232,w0,w1,w2,w3,w68,w4,w5] [118,179,204,405,491,577] [n454,n483,n481] (by decide +kernel)
def n485 := cc 8 [w0,w1,w2,w242,w3,w4,w5] [0,143,233,269,517,521,662] [] (by decide +kernel)
def n486 := cc 9 [w232,w0,w1,w2,w3,w4,w5,w13] [143,231,351,360,389,459,517,521,577,641,675] [n455,n483,n485,n431,n440,n438,v168] (by decide +kernel)
def n487 := cc 8 [w243,w0,w1,w2,w3,w4,w5] [143,161,517,577] [] (by decide +kernel)
def n488 := cc 8 [w70,w71,w232,w0,w1,w2,w3] [163,250,405,491,577] [n456,n482] (by decide +kernel)
def n489 := cc 9 [w70,w232,w0,w1,w2,w3,w4,w5] [90,143,161,491,517,577] [n488,n457,n439,n487] (by decide +kernel)
def v180 : Closed T 9 := rotateClosed n477 auto1 auto1ok
def v181 : Closed T 9 := rotateClosed n489 auto1 auto1ok
def v182 : Closed T 9 := rotateClosed n479 auto1 auto1ok
def v183 : Closed T 9 := rotateClosed n466 auto1 auto1ok
def v184 : Closed T 9 := rotateClosed n473 auto1 auto1ok
def v185 : Closed T 9 := rotateClosed n464 auto1 auto1ok
def v186 : Closed T 9 := rotateClosed n475 auto1 auto1ok
def v187 : Closed T 9 := rotateClosed n442 auto1 auto1ok
def n490 := cc 10 [w232,w0,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n477,v180,n489,v181,n479,v182,n462,n466,v183,n458,n473,v184,n460,n484,n464,v185,n475,v186,n486,n435,n442,v187] (by decide +kernel)
def n491 := cc 8 [w115,w0,w1,w2,w3,w4,w244,w5] [379,597,672] [] (by decide +kernel)
def n492 := cc 8 [w0,w1,w2,w3,w4,w245,w121] [136,222,664] [] (by decide +kernel)
def n493 := cc 8 [w126,w0,w1,w2,w3,w244,w5] [448,672] [] (by decide +kernel)
def n494 := cc 8 [w65,w0,w1,w2,w3,w4,w244,w5] [379,597,656,666] [] (by decide +kernel)
def n495 := cc 8 [w0,w1,w2,w3,w4,w245,w13] [90,231,389,655,671] [] (by decide +kernel)
def n496 := cc 8 [w70,w0,w1,w2,w3,w244,w5] [247,597,666] [] (by decide +kernel)
def n497 := cc 8 [w0,w1,w2,w3,w4,w5,w246] [83,90,179,231,269,598] [] (by decide +kernel)
def n498 := cc 8 [w247,w0,w1,w2,w3,w4,w5] [247,512,672] [] (by decide +kernel)
def v188 : Closed T 8 := rotateClosed n492 auto1 auto1ok
def v189 : Closed T 8 := rotateClosed n495 auto1 auto1ok
def n499 := cc 9 [w0,w1,w2,w3,w4,w244,w5] [83,97,184,269,459,512,597,672] [n494,n496,n498,n491,n493,n344,n191,n497,v188,v189] (by decide +kernel)
def n500 := cc 8 [w113,w237,w0,w1,w3,w4,w5] [3,164,208,362,597,655] [] (by decide +kernel)
def n501 := cc 9 [w237,w0,w1,w2,w3,w112,w4,w5] [97,208,269,597,655] [n500] (by decide +kernel)
def n502 := cc 8 [w237,w0,w1,w116,w3,w4,w5] [97,377,671,672] [] (by decide +kernel)
def n503 := cc 8 [w237,w0,w1,w2,w3,w4,w117,w5] [252,671,674] [] (by decide +kernel)
def n504 := cc 8 [w237,w115,w0,w1,w3,w4,w9,w5] [183,380,597,672] [] (by decide +kernel)
def n505 := cc 8 [w237,w115,w0,w1,w2,w4,w12,w5] [138,179,253,377,597,655] [] (by decide +kernel)
def n506 := cc 7 [w237,w115,w220,w1,w2,w3,w4,w5] [671,672,673] [] (by decide +kernel)
def n507 := cc 8 [w237,w115,w0,w1,w2,w3,w4,w5,w13] [251,377,655,671,672,673,674] [n506] (by decide +kernel)
def v190 : Closed T 8 := rotateClosed n505 auto1 auto1ok
def v191 : Closed T 8 := rotateClosed n504 auto1 auto1ok
def v192 : Closed T 8 := rotateClosed n503 auto1 auto1ok
def v193 : Closed T 8 := rotateClosed n491 auto1 auto1ok
def n508 := cc 9 [w237,w115,w0,w1,w2,w3,w4,w5] [0,97,251,377,597,655] [n507,n505,v190,n504,v191,n503,v192,n502,n491,v193] (by decide +kernel)
def n509 := cc 8 [w237,w0,w1,w3,w4,w121,w15] [95,97,222,655,670,671] [] (by decide +kernel)
def n510 := cc 8 [w124,w237,w0,w1,w3,w4,w5] [97,669,672] [] (by decide +kernel)
def n511 := cc 8 [w237,w0,w1,w2,w3,w4,w121,w13] [223,655,671,672,675] [] (by decide +kernel)
def n512 := cc 8 [w237,w0,w1,w2,w3,w4,w5,w125] [77,218,377,671,672,675] [] (by decide +kernel)
def v194 : Closed T 8 := rotateClosed n511 auto1 auto1ok
def v195 : Closed T 8 := rotateClosed n509 auto1 auto1ok
def n513 := cc 9 [w237,w0,w1,w2,w3,w4,w123,w5] [97,214,377,389,597,671,672,675] [n510,n512,v194,v195,n191,v188] (by decide +kernel)
def n514 := cc 8 [w237,w0,w1,w127,w3,w4,w5] [97,448,672] [] (by decide +kernel)
def n515 := cc 8 [w237,w0,w1,w2,w3,w4,w129,w5] [143,259,655,671,672] [] (by decide +kernel)
def n516 := cc 8 [w237,w126,w0,w1,w3,w9,w5] [448,672] [] (by decide +kernel)
def n517 := cc 8 [w237,w126,w0,w1,w2,w3,w5,w13] [143,256,597,671,672] [] (by decide +kernel)
def v196 : Closed T 8 := rotateClosed n515 auto1 auto1ok
def n518 := cc 9 [w237,w126,w0,w1,w2,w3,w4,w5] [97,254,502,597,671] [n517,n516,v196,n514,n493,n344] (by decide +kernel)
def n519 := cc 8 [w0,w248,w1,w3,w4,w9,w5] [184,390,672] [] (by decide +kernel)
def n520 := cc 8 [w65,w237,w0,w1,w3,w4,w9,w5] [245,597,672] [] (by decide +kernel)
def n521 := cc 8 [w237,w0,w1,w3,w4,w15,w13] [231,655,671,675] [] (by decide +kernel)
def n522 := cc 8 [w70,w237,w0,w1,w3,w9,w5] [231,247,597,671] [] (by decide +kernel)
def n523 := cc 8 [w237,w0,w1,w3,w4,w5,w44] [179,231,247,266,599,657] [] (by decide +kernel)
def n524 := cc 8 [w46,w237,w0,w1,w3,w4,w5] [247,512,672] [] (by decide +kernel)
def v197 : Closed T 8 := rotateClosed n521 auto1 auto1ok
def n525 := cc 9 [w237,w0,w1,w3,w4,w9,w5] [97,184,512,597,676] [n520,n522,n524,n504,n516,n523,v195,v197,n519,n318] (by decide +kernel)
def n526 := cc 8 [w0,w1,w2,w3,w249,w4,w5] [90,179,377,448,459] [] (by decide +kernel)
def n527 := cc 8 [w237,w0,w1,w3,w200,w4,w5] [179,377,448,512] [] (by decide +kernel)
def n528 := cc 8 [w237,w0,w1,w2,w3,w4,w61] [199,377,671] [n443] (by decide +kernel)
def n529 := cc 8 [w237,w0,w1,w2,w3,w4,w100,w5] [179,202,597,676] [] (by decide +kernel)
def n530 := cc 8 [w63,w237,w0,w1,w2,w3,w5] [117,203,294,377,448,502] [n444] (by decide +kernel)
def n531 := cc 7 [w64,w237,w0,w1,w2,w4] [26,182,377,511,597,655] [n445] (by decide +kernel)
def v198 : Closed T 7 := rotateClosed n531 auto1 auto1ok
def n532 := cc 8 [w237,w0,w1,w2,w60,w12,w5] [26,112,200,377,655] [v198,n446] (by decide +kernel)
def v199 : Closed T 8 := rotateClosed n530 auto1 auto1ok
def v200 : Closed T 8 := rotateClosed n529 auto1 auto1ok
def n533 := cc 9 [w237,w0,w1,w2,w60,w3,w4,w5] [198,377,502,671] [v199,n447,n532,v200,n528,n527,n526] (by decide +kernel)
def n534 := cc 8 [w0,w250,w1,w2,w3,w4,w5] [179,225,597,655] [] (by decide +kernel)
def n535 := cc 8 [w237,w203,w0,w1,w2,w3,w4,w5] [26,183,228,597,655] [] (by decide +kernel)
def n536 := cc 9 [w237,w0,w1,w2,w3,w4,w12,w5] [26,138,225,597,655] [n448,n505,n535,n532,n534] (by decide +kernel)
def n537 := cc 8 [w65,w66,w237,w0,w1,w2,w4] [26,160,246,377,597] [n449,n531] (by decide +kernel)
def n538 := cc 9 [w65,w237,w0,w1,w2,w3,w4,w5] [245,294,377,655,675] [n537,n450,n520,n494] (by decide +kernel)
def n539 := cc 8 [w251,w0,w1,w2,w3,w4,w5] [179,261,655] [] (by decide +kernel)
def n540 := cc 8 [w237,w0,w1,w214,w3,w4,w5] [179,261,655] [] (by decide +kernel)
def v201 : Closed T 8 := rotateClosed n537 auto1 auto1ok
def n541 := cc 9 [w67,w237,w0,w1,w2,w3,w4,w5] [261,655,671] [v201,n451,n540,n539] (by decide +kernel)
def n542 := cc 7 [w0,w1,w2,w3,w252,w13] [180,206,597] [] (by decide +kernel)
def n543 := cc 8 [w0,w1,w2,w3,w4,w252,w5] [179,448,502,597] [n542] (by decide +kernel)
def n544 := cc 7 [w237,w0,w1,w3,w217,w13] [180,206,597] [] (by decide +kernel)
def n545 := cc 8 [w237,w0,w1,w3,w4,w217,w5] [179,204,448,502] [n544] (by decide +kernel)
def n546 := cc 7 [w69,w237,w0,w1,w2,w3] [448,512,597,671] [n452] (by decide +kernel)
def n547 := cc 7 [w69,w237,w0,w1,w2,w3,w13] [448,512,597,671,675] [] (by decide +kernel)
def n548 := cc 8 [w237,w0,w1,w2,w3,w68,w13] [206,597,671] [n546,n547,n453,n544,n542] (by decide +kernel)
def n549 := cc 9 [w237,w0,w1,w2,w3,w68,w4,w5] [204,502,597,671] [n454,n548,n545,n543] (by decide +kernel)
def n550 := cc 8 [w0,w253,w1,w2,w3,w4,w5] [179,231,269,600,658] [] (by decide +kernel)
def n551 := cc 8 [w237,w220,w0,w1,w2,w3,w4,w5] [77,233,377,505,672,675] [n506] (by decide +kernel)
def n552 := cc 8 [w237,w0,w1,w2,w226,w3,w4,w5,w13] [232,655,662,671,675,676] [] (by decide +kernel)
def v202 : Closed T 8 := rotateClosed n517 auto1 auto1ok
def n553 := cc 9 [w237,w0,w1,w2,w3,w4,w5,w13] [97,231,351,377,389,459,597,655,662,675,676] [n455,n507,n517,v202,n551,n552,n548,n512,n511,v194,n523,n521,v197,n550,n431,n497,n495,v189] (by decide +kernel)
def n554 := cc 8 [w254,w0,w1,w2,w3,w4,w5] [179,247,448,597] [] (by decide +kernel)
def n555 := cc 8 [w237,w0,w1,w229,w3,w4,w5] [179,247,448,597] [] (by decide +kernel)
def n556 := cc 8 [w70,w71,w237,w0,w1,w2,w3] [163,250,405,502,597] [n456,n546] (by decide +kernel)
def n557 := cc 9 [w70,w237,w0,w1,w2,w3,w4,w5] [231,247,502,597,671] [n556,n457,n522,n496,n555,n554] (by decide +kernel)
def v203 : Closed T 9 := rotateClosed n538 auto1 auto1ok
def v204 : Closed T 9 := rotateClosed n557 auto1 auto1ok
def v205 : Closed T 9 := rotateClosed n541 auto1 auto1ok
def v206 : Closed T 9 := rotateClosed n518 auto1 auto1ok
def v207 : Closed T 9 := rotateClosed n533 auto1 auto1ok
def v208 : Closed T 9 := rotateClosed n513 auto1 auto1ok
def v209 : Closed T 9 := rotateClosed n536 auto1 auto1ok
def v210 : Closed T 9 := rotateClosed n525 auto1 auto1ok
def v211 : Closed T 9 := rotateClosed n499 auto1 auto1ok
def n558 := cc 10 [w237,w0,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n538,v203,n557,v204,n541,v205,n458,n508,n518,v206,n533,v207,n501,n549,n513,v208,n536,v209,n553,n525,v210,n435,n499,v211] (by decide +kernel)
def n559 := cc 8 [w0,w1,w256,w3,w4,w9,w5] [97,179,521,556] [] (by decide +kernel)
def n560 := cc 8 [w118,w0,w1,w256,w3,w4,w5] [155,178,521,632] [] (by decide +kernel)
def n561 := cc 8 [w0,w1,w2,w3,w4,w257,w5] [83,90,179,331,459,556] [] (by decide +kernel)
def n562 := cc 8 [w258,w0,w1,w2,w3,w4,w5] [83,90,178,369,389] [] (by decide +kernel)
def n563 := cc 8 [w0,w1,w2,w256,w3,w4,w5,w13] [351,521,662,675] [] (by decide +kernel)
def v212 : Closed T 8 := rotateClosed n560 auto1 auto1ok
def v213 : Closed T 8 := rotateClosed n562 auto1 auto1ok
def v214 : Closed T 8 := rotateClosed n561 auto1 auto1ok
def v215 : Closed T 8 := rotateClosed n559 auto1 auto1ok
def n564 := cc 9 [w0,w1,w2,w256,w3,w4,w5] [97,178,179,269,556,632] [n560,v212,n562,v213,n563,n561,v214,n559,v215] (by decide +kernel)
def n565 := cc 8 [w0,w1,w2,w3,w4,w259,w15] [179,184,345,664] [] (by decide +kernel)
def n566 := cc 8 [w261,w0,w1,w2,w3,w4,w5] [165,179,521,577] [] (by decide +kernel)
def n567 := cc 8 [w0,w1,w2,w3,w4,w259,w13] [90,143,517,564,672] [] (by decide +kernel)
def n568 := cc 8 [w0,w1,w2,w3,w4,w5,w262] [83,90,143,179,184,564,636] [] (by decide +kernel)
def n569 := cc 8 [w263,w0,w1,w2,w3,w4,w5] [90,161,581,666] [] (by decide +kernel)
def v216 : Closed T 8 := rotateClosed n565 auto1 auto1ok
def v217 : Closed T 8 := rotateClosed n567 auto1 auto1ok
def n570 := cc 9 [w0,w1,w2,w3,w4,w260,w5] [97,184,459,524,666,675] [n569,n566,n561,n568,v216,v217] (by decide +kernel)
def n571 := cc 7 [w265,w264,w1,w2,w4,w5] [98,178,182,597,655] [] (by decide +kernel)
def n572 := cc 7 [w264,w1,w2,w266,w4,w5] [3,123,179,182,577,641] [] (by decide +kernel)
def n573 := cc 7 [w267,w264,w1,w2,w4,w5] [164,179,182,556,632] [] (by decide +kernel)
def n574 := cc 7 [w264,w268,w1,w2,w4,w5] [60,148,178,182,530,612] [] (by decide +kernel)
def n575 := cc 8 [w264,w1,w2,w4,w5] [97,524,607] [n573,n571,n574,n572] (by decide +kernel)
def n576 := cc 9 [w255,w1,w2,w112,w4,w5] [97,524,607] [n575] (by decide +kernel)
def n577 := cc 8 [w269,w0,w1,w2,w3,w4,w5] [152,331,672] [] (by decide +kernel)
def n578 := cc 9 [w255,w0,w1,w2,w3,w4,w9,w5] [127,184,524,672] [n577,n561,v216,n559] (by decide +kernel)
def n579 := cc 8 [w270,w0,w1,w2,w3,w4,w5] [83,178,369,389,632] [] (by decide +kernel)
def n580 := cc 9 [w118,w255,w0,w1,w2,w3,w4,w5] [185,369,607,672,675] [n560,n579] (by decide +kernel)
def n581 := cc 8 [w271,w0,w1,w2,w3,w4,w5] [143,184,351,662,671,672] [] (by decide +kernel)
def n582 := cc 9 [w255,w0,w1,w2,w3,w4,w5,w13] [185,231,351,389,607,672,675] [n581,n563,n568,n567,v217] (by decide +kernel)
def v218 : Closed T 9 := rotateClosed n580 auto1 auto1ok
def v219 : Closed T 9 := rotateClosed n578 auto1 auto1ok
def v220 : Closed T 9 := rotateClosed n570 auto1 auto1ok
def n583 := cc 10 [w255,w0,w1,w2,w3,w4,w5] [97,184,269,524,607] [n580,v218,n578,v219,n582,n576,n564,n570,v220] (by decide +kernel)
def n584 := cc 8 [w1,w273,w2,w3,w112,w4,w5] [208,294,541,623] [] (by decide +kernel)
def n585 := cc 8 [w274,w0,w1,w2,w3,w4,w5] [164,360,540,622] [] (by decide +kernel)
def n586 := cc 8 [w113,w0,w272,w1,w3,w4,w5] [79,164,208,540,622] [] (by decide +kernel)
def n587 := cc 9 [w0,w272,w1,w2,w3,w112,w4,w5] [97,208,269,540,622] [n586,n585,n584] (by decide +kernel)
def n588 := cc 8 [w275,w0,w1,w2,w3,w4,w5] [10,179,585,648] [] (by decide +kernel)
def n589 := cc 8 [w39,w113,w0,w1,w3,w4,w5] [164,361,585,648] [] (by decide +kernel)
def n590 := cc 9 [w39,w0,w1,w2,w3,w112,w4,w5] [97,208,269,585,648] [n588,n589] (by decide +kernel)
def n591 := cc 8 [w0,w1,w2,w42,w112,w4,w5] [123,208,269,573,638] [] (by decide +kernel)
def n592 := cc 9 [w0,w41,w1,w2,w112,w4,w5] [97,184,269,524,607] [n591] (by decide +kernel)
def n593 := cc 8 [w0,w1,w2,w277,w3,w4,w5] [179,208,573,638] [] (by decide +kernel)
def n594 := cc 8 [w0,w276,w1,w2,w277,w3,w4,w5] [182,208,573,638] [] (by decide +kernel)
def n595 := cc 9 [w0,w276,w1,w2,w3,w4,w5] [97,182,208,524,607] [n588,n594,n593] (by decide +kernel)
def n596 := cc 9 [w164,w0,w1,w2,w112,w4,w5] [97,179,184,269,524,607] [] (by decide +kernel)
def n597 := cc 8 [w0,w278,w1,w2,w3,w4,w5] [164,208,361,540,622] [] (by decide +kernel)
def n598 := cc 9 [w113,w0,w1,w2,w3,w4,w5] [164,179,269,511,524,607] [n588,n589,n500,n586,n176,n597] (by decide +kernel)
def n599 := cc 10 [w0,w1,w2,w3,w112,w4,w5] [97,184,269,524,607] [n590,n596,n598,n501,n576,n587,n592,n595,n177] (by decide +kernel)
def n600 := cc 9 [w0,w280,w2,w3,w4,w5] [0,97,184,389] [] (by decide +kernel)
def n601 := cc 9 [w0,w281,w2,w3,w4,w5] [97,524,607] [] (by decide +kernel)
def n602 := cc 9 [w0,w1,w2,w282,w3,w4,w5] [97,524,607] [] (by decide +kernel)
def n603 := cc 9 [w279,w115,w1,w2,w4,w5] [97,269,524,607] [n575] (by decide +kernel)
def n604 := cc 10 [w279,w0,w1,w2,w3,w4,w5] [97,184,524,607] [n603,n601,n602,n600] (by decide +kernel)
def n605 := cc 8 [w0,w1,w2,w3,w4,w283,w5] [83,90,179,331,459,577] [] (by decide +kernel)
def n606 := cc 8 [w284,w0,w1,w2,w3,w4,w5] [90,369,672] [] (by decide +kernel)
def n607 := cc 8 [w0,w1,w2,w116,w3,w4,w5,w13] [83,351,641,662,671] [] (by decide +kernel)
def v221 : Closed T 8 := rotateClosed n606 auto1 auto1ok
def v222 : Closed T 8 := rotateClosed n605 auto1 auto1ok
def n608 := cc 9 [w0,w1,w2,w116,w3,w4,w5] [0,97,269,389,641,671,672] [n606,v221,n502,n607,n605,v222,n178] (by decide +kernel)
def n609 := cc 8 [w0,w1,w2,w3,w4,w285,w121] [142,179,327,664] [] (by decide +kernel)
def n610 := cc 8 [w286,w0,w1,w2,w3,w4,w5] [179,388,521,556] [] (by decide +kernel)
def n611 := cc 7 [w0,w1,w2,w3,w117,w15,w13] [86,348,518,671] [] (by decide +kernel)
def n612 := cc 8 [w0,w1,w2,w3,w4,w117,w5,w15] [345,518,666,671] [n611] (by decide +kernel)
def n613 := cc 8 [w118,w0,w1,w2,w3,w4,w117,w5] [252,521,589,674] [] (by decide +kernel)
def v223 : Closed T 7 := rotateClosed n611 auto1 auto1ok
def n614 := cc 8 [w0,w1,w2,w3,w4,w285,w13] [90,351,389,517,673] [v223] (by decide +kernel)
def n615 := cc 8 [w0,w1,w2,w3,w4,w5,w287] [83,90,179,183,184,351] [] (by decide +kernel)
def n616 := cc 8 [w288,w0,w1,w2,w3,w4,w5] [90,374,564,674] [] (by decide +kernel)
def v224 : Closed T 8 := rotateClosed n609 auto1 auto1ok
def v225 : Closed T 8 := rotateClosed n614 auto1 auto1ok
def n617 := cc 9 [w0,w1,w2,w3,w4,w117,w5] [184,269,459,524,674,681] [n613,n616,n610,n503,n179,n612,n605,n615,v224,v225] (by decide +kernel)
def n618 := cc 8 [w115,w0,w1,w2,w3,w4,w121,w15] [183,251,328,607,670,671] [] (by decide +kernel)
def n619 := cc 8 [w115,w0,w1,w2,w3,w4,w121,w13] [53,329,672,674,675] [] (by decide +kernel)
def n620 := cc 8 [w115,w0,w1,w2,w3,w4,w5,w125] [83,218,251,320,636,672,675] [] (by decide +kernel)
def v226 : Closed T 8 := rotateClosed n618 auto1 auto1ok
def v227 : Closed T 8 := rotateClosed n619 auto1 auto1ok
def n621 := cc 9 [w115,w0,w1,w2,w3,w4,w123,w5] [251,315,524,636,673,675] [n182,n620,v226,v227,v224] (by decide +kernel)
def n622 := cc 9 [w115,w0,w1,w2,w8,w4,w5] [97,179,184,269,524,607] [] (by decide +kernel)
def n623 := cc 8 [w0,w289,w1,w2,w3,w4,w5] [331,530,674] [] (by decide +kernel)
def n624 := cc 8 [w115,w167,w0,w1,w2,w3,w4,w5] [342,597,672] [] (by decide +kernel)
def n625 := cc 8 [w115,w0,w1,w2,w3,w4,w15,w13] [251,348,607,671,673,675] [n611] (by decide +kernel)
def n626 := cc 6 [w45,w290,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n627 := cc 6 [w115,w45,w41,w1,w2,w4,w5] [89,96,179] [] (by decide +kernel)
def n628 := cc 7 [w115,w45,w1,w2,w3,w4,w5] [179,576,640] [n63,n627,n626] (by decide +kernel)
def n629 := cc 8 [w115,w0,w1,w2,w3,w4,w5,w44] [179,183,339,574,639] [n628] (by decide +kernel)
def n630 := cc 8 [w46,w115,w0,w1,w2,w3,w4,w5] [90,343,589,672] [] (by decide +kernel)
def v228 : Closed T 8 := rotateClosed n625 auto1 auto1ok
def v229 : Closed T 8 := rotateClosed n612 auto1 auto1ok
def n631 := cc 9 [w115,w0,w1,w2,w3,w4,w9,w5] [97,251,331,504,512,524,672] [n630,n504,n624,n182,n629,v226,v228,n180,n623,v229,n605] (by decide +kernel)
def n632 := cc 8 [w291,w0,w1,w2,w3,w4,w5] [83,183,251,389,641] [] (by decide +kernel)
def n633 := cc 8 [w115,w0,w292,w1,w2,w3,w4,w5] [178,370,672,674] [] (by decide +kernel)
def n634 := cc 8 [w115,w0,w1,w2,w3,w4,w177,w5] [183,371,589,672] [] (by decide +kernel)
def n635 := cc 9 [w118,w115,w0,w1,w2,w3,w4,w5] [97,251,369,450,607,675] [n181,n613,n633,n634,n632] (by decide +kernel)
def n636 := cc 8 [w55,w115,w0,w1,w2,w4,w5] [179,388,524,607] [] (by decide +kernel)
def n637 := cc 9 [w115,w0,w1,w2,w4,w12,w5] [138,269,524,607] [n636,n505,n184] (by decide +kernel)
def n638 := cc 8 [w0,w293,w1,w2,w3,w4,w5] [179,183,184,351,535,617] [] (by decide +kernel)
def n639 := cc 8 [w115,w220,w0,w1,w2,w3,w4,w5] [251,356,505,672,674,675] [n506] (by decide +kernel)
def n640 := cc 8 [w47,w115,w0,w1,w2,w3,w4,w5] [179,183,357,603,661] [] (by decide +kernel)
def n641 := cc 9 [w115,w0,w1,w2,w3,w4,w5,w13] [97,231,251,351,524,607,675,687] [n640,n507,n639,n185,n620,n629,n619,v227,n625,v228,n638,n607,n615,n614,v225] (by decide +kernel)
def v230 : Closed T 9 := rotateClosed n635 auto1 auto1ok
def v231 : Closed T 9 := rotateClosed n621 auto1 auto1ok
def v232 : Closed T 9 := rotateClosed n631 auto1 auto1ok
def v233 : Closed T 9 := rotateClosed n637 auto1 auto1ok
def v234 : Closed T 9 := rotateClosed n617 auto1 auto1ok
def n642 := cc 10 [w115,w0,w1,w2,w3,w4,w5] [97,184,269,524,607] [n635,v230,n603,n508,n186,n621,v231,n631,v232,n641,n622,n637,v233,n608,n617,v234] (by decide +kernel)
def n643 := cc 9 [w0,w295,w2,w3,w4,w5] [97,184,269,389] [] (by decide +kernel)
def n644 := cc 7 [w297,w0,w2,w3,w4,w299] [102,192,538] [] (by decide +kernel)
def n645 := cc 6 [w301,w302,w0,w3,w4] [512,620,668] [] (by decide +kernel)
def v235 : Closed T 6 := rotateClosed n645 auto1 auto1ok
def n646 := cc 7 [w297,w0,w298,w3,w9,w5] [103,179,538] [v235] (by decide +kernel)
def n647 := cc 8 [w297,w0,w298,w2,w3,w4,w5] [9,101,192,281,394,469] [n646,n644] (by decide +kernel)
def n648 := cc 8 [w297,w0,w2,w3,w4,w9,w5] [127,192,394,639] [n646] (by decide +kernel)
def n649 := cc 7 [w118,w181,w302,w0,w3,w4] [157,187,447,464] [n645] (by decide +kernel)
def n650 := cc 8 [w118,w302,w0,w2,w3,w4,w5] [136,155,187,464,589] [n649] (by decide +kernel)
def v236 : Closed T 7 := rotateClosed n649 auto1 auto1ok
def n651 := cc 8 [w179,w297,w0,w2,w3,w4,w5] [127,165,192,508,538] [v236] (by decide +kernel)
def v237 : Closed T 8 := rotateClosed n650 auto1 auto1ok
def n652 := cc 9 [w297,w0,w2,w3,w4,w5] [97,607] [v237,n651,n647,n648] (by decide +kernel)
def n653 := cc 7 [w0,w1,w303,w3,w304,w5] [178,465,550] [] (by decide +kernel)
def n654 := cc 6 [w307,w0,w1,w3,w4] [178,465,512,618] [] (by decide +kernel)
def v238 : Closed T 6 := rotateClosed n654 auto1 auto1ok
def n655 := cc 7 [w0,w1,w309,w3,w310,w5] [103,179,536] [v238] (by decide +kernel)
def v239 : Closed T 7 := rotateClosed n653 auto1 auto1ok
def n656 := cc 8 [w0,w1,w309,w308,w3,w4,w5] [178,469,536] [n655,v239] (by decide +kernel)
def v240 : Closed T 7 := rotateClosed n655 auto1 auto1ok
def n657 := cc 8 [w0,w1,w303,w3,w4,w5,w306] [136,178,465,574] [v240] (by decide +kernel)
def n658 := cc 7 [w311,w312,w0,w1,w3,w4] [157,178,465,593] [n654] (by decide +kernel)
def n659 := cc 8 [w311,w0,w1,w303,w3,w4,w5] [136,178,445,465,589] [n658] (by decide +kernel)
def v241 : Closed T 7 := rotateClosed n658 auto1 auto1ok
def n660 := cc 8 [w313,w0,w1,w308,w3,w4,w5] [127,165,178,395,508,536] [v241] (by decide +kernel)
def v242 : Closed T 8 := rotateClosed n660 auto1 auto1ok
def v243 : Closed T 8 := rotateClosed n656 auto1 auto1ok
def n661 := cc 9 [w0,w1,w303,w3,w4,w5] [97,524] [n659,v242,v243,n657] (by decide +kernel)
def n662 := cc 6 [w314,w0,w1,w3,w4] [178,188,512,618] [] (by decide +kernel)
def v244 : Closed T 6 := rotateClosed n662 auto1 auto1ok
def n663 := cc 7 [w0,w1,w298,w3,w310,w5] [83,103,536] [v244] (by decide +kernel)
def n664 := cc 8 [w0,w1,w298,w308,w3,w4,w5] [178,469,536] [n663,v239] (by decide +kernel)
def n665 := cc 8 [w0,w1,w303,w3,w4,w5,w15] [136,178,459,465,574] [] (by decide +kernel)
def n666 := cc 8 [w118,w0,w1,w303,w3,w4,w5] [136,178,445,459,589] [] (by decide +kernel)
def n667 := cc 7 [w311,w181,w0,w1,w3,w4] [90,157,465,593] [n662] (by decide +kernel)
def v245 : Closed T 7 := rotateClosed n667 auto1 auto1ok
def n668 := cc 8 [w179,w0,w1,w308,w3,w4,w5] [127,165,178,395,508,536] [v245] (by decide +kernel)
def n669 := cc 8 [w0,w1,w2,w3,w4,w310,w5] [83,127,165,193,639] [n663] (by decide +kernel)
def n670 := cc 8 [w311,w0,w1,w2,w3,w4,w5] [90,178,445,589] [n667] (by decide +kernel)
def v246 : Closed T 8 := rotateClosed n668 auto1 auto1ok
def v247 : Closed T 8 := rotateClosed n664 auto1 auto1ok
def v248 : Closed T 8 := rotateClosed n669 auto1 auto1ok
def n671 := cc 9 [w0,w1,w2,w303,w3,w4,w5] [97,178,179,459,524] [n666,n670,v246,v247,v248,n665] (by decide +kernel)
def n672 := cc 9 [w315,w0,w1,w3,w4,w5] [97,184,607] [] (by decide +kernel)
def n673 := cc 9 [w0,w1,w2,w316,w4,w5] [97,389,607] [] (by decide +kernel)
def n674 := cc 7 [w317,w0,w1,w2,w4,w299] [102,196,285,398] [] (by decide +kernel)
def n675 := cc 6 [w301,w318,w0,w1,w4] [190,512,672] [] (by decide +kernel)
def v249 : Closed T 6 := rotateClosed n675 auto1 auto1ok
def n676 := cc 7 [w317,w0,w1,w298,w9,w5] [103,179,196,286,470] [v249] (by decide +kernel)
def n677 := cc 8 [w317,w0,w1,w298,w2,w4,w5] [101,196,283,398,469] [n676,n674] (by decide +kernel)
def n678 := cc 8 [w317,w0,w1,w2,w4,w9,w5] [127,196,331,398,487] [n676] (by decide +kernel)
def n679 := cc 7 [w118,w181,w318,w0,w1,w4] [157,190,373,447,467] [n675] (by decide +kernel)
def n680 := cc 8 [w118,w318,w0,w1,w2,w4,w5] [136,155,190,369,445,467] [n679] (by decide +kernel)
def v250 : Closed T 7 := rotateClosed n679 auto1 auto1ok
def n681 := cc 8 [w179,w317,w0,w1,w2,w4,w5] [127,165,196,388,398,508] [v250] (by decide +kernel)
def v251 : Closed T 8 := rotateClosed n680 auto1 auto1ok
def n682 := cc 9 [w317,w0,w1,w2,w4,w5] [97,269,459] [v251,n681,n677,n678] (by decide +kernel)
def n683 := cc 7 [w0,w1,w2,w3,w319,w299] [102,193,469,535] [] (by decide +kernel)
def n684 := cc 6 [w322,w0,w1,w3,w4] [188,512,672] [] (by decide +kernel)
def v252 : Closed T 6 := rotateClosed n684 auto1 auto1ok
def n685 := cc 7 [w0,w1,w323,w3,w310,w5] [83,103,193,629] [v252] (by decide +kernel)
def n686 := cc 8 [w0,w1,w323,w2,w3,w319,w5] [83,101,165,193,627] [n685,n683] (by decide +kernel)
def v253 : Closed T 7 := rotateClosed n685 auto1 auto1ok
def n687 := cc 8 [w0,w1,w2,w3,w4,w320,w306] [90,136,171,188,574] [v253] (by decide +kernel)
def n688 := cc 7 [w324,w325,w0,w1,w3,w4] [157,179,188,593] [n684] (by decide +kernel)
def n689 := cc 8 [w324,w0,w1,w2,w3,w4,w320] [90,155,188,589] [n688] (by decide +kernel)
def v254 : Closed T 7 := rotateClosed n688 auto1 auto1ok
def n690 := cc 8 [w326,w0,w1,w2,w3,w319,w5] [83,165,193,661] [v254] (by decide +kernel)
def v255 : Closed T 8 := rotateClosed n690 auto1 auto1ok
def v256 : Closed T 8 := rotateClosed n686 auto1 auto1ok
def n691 := cc 9 [w0,w1,w2,w3,w4,w320] [97,524] [n689,v255,v256,n687] (by decide +kernel)
def n692 := cc 8 [w0,w1,w298,w2,w3,w319,w5] [83,101,165,193,469,535] [n663,n683] (by decide +kernel)
def n693 := cc 8 [w0,w1,w2,w3,w4,w320,w15] [90,136,171,184,574] [] (by decide +kernel)
def n694 := cc 7 [w118,w325,w0,w1,w3,w4] [157,179,188,593] [n662] (by decide +kernel)
def n695 := cc 8 [w118,w0,w1,w2,w3,w4,w320] [90,155,188,589] [n694] (by decide +kernel)
def n696 := cc 8 [w179,w0,w1,w2,w3,w319,w5] [83,101,165,184,193,394,508,535] [] (by decide +kernel)
def v257 : Closed T 7 := rotateClosed n694 auto1 auto1ok
def n697 := cc 8 [w326,w0,w1,w2,w3,w4,w5] [83,165,193,661] [v257] (by decide +kernel)
def v258 : Closed T 8 := rotateClosed n695 auto1 auto1ok
def v259 : Closed T 8 := rotateClosed n693 auto1 auto1ok
def n698 := cc 9 [w0,w1,w2,w3,w4,w319,w5] [83,97,184,607,662] [v258,n696,n697,n692,n669,v259] (by decide +kernel)
def n699 := cc 9 [w327,w0,w1,w2,w3,w5] [97,459,524] [] (by decide +kernel)
def n700 := cc 8 [w328,w1,w2,w3,w4,w121] [] [] (by decide +kernel)
def n701 := cc 7 [w294,w1,w2,w3,w123,w330] [189,531,669] [] (by decide +kernel)
def n702 := cc 7 [w332,w296,w1,w2,w3,w121] [] [] (by decide +kernel)
def v260 : Closed T 7 := rotateClosed n702 auto1 auto1ok
def n703 := cc 8 [w294,w1,w329,w2,w3,w123,w5] [189,466,530,664,669] [v260,n701] (by decide +kernel)
def n704 := cc 7 [w328,w1,w2,w3,w4,w141] [] [] (by decide +kernel)
def n705 := cc 7 [w333,w1,w2,w3,w4,w121] [] [] (by decide +kernel)
def v261 : Closed T 7 := rotateClosed n704 auto1 auto1ok
def v262 : Closed T 7 := rotateClosed n705 auto1 auto1ok
def n706 := cc 8 [w294,w1,w2,w3,w123,w119,w5] [83,127,179,466,556,664] [v261,v262] (by decide +kernel)
def n707 := cc 8 [w334,w296,w1,w2,w3,w4,w121] [] [] (by decide +kernel)
def n708 := cc 7 [w124,w335,w1,w2,w3,w5] [179,577,669] [] (by decide +kernel)
def n709 := cc 7 [w334,w122,w296,w1,w3,w4] [] [] (by decide +kernel)
def v263 : Closed T 7 := rotateClosed n709 auto1 auto1ok
def n710 := cc 8 [w124,w294,w1,w2,w3,w123,w5] [179,466,577,664,669] [v263,n708] (by decide +kernel)
def n711 := cc 6 [w301,w294,w1,w3,w123] [178,189,619,666] [] (by decide +kernel)
def n712 := cc 7 [w294,w1,w300,w3,w123,w15] [108,179,666] [n711] (by decide +kernel)
def n713 := cc 8 [w294,w1,w300,w2,w3,w123,w5] [189,550,666] [n712] (by decide +kernel)
def n714 := cc 8 [w294,w1,w2,w3,w123,w5,w15] [136,574,664,671] [n712] (by decide +kernel)
def n715 := cc 7 [w118,w181,w294,w1,w3,w123] [157,189,666] [n711] (by decide +kernel)
def n716 := cc 8 [w118,w294,w1,w2,w3,w123,w5] [189,589,675] [n715] (by decide +kernel)
def n717 := cc 8 [w179,w296,w1,w2,w3,w4,w121] [] [] (by decide +kernel)
def n718 := cc 6 [w337,w294,w1,w2,w3] [466,619,662,666] [] (by decide +kernel)
def n719 := cc 7 [w294,w1,w2,w3,w336,w125] [83,121,466,537] [n718] (by decide +kernel)
def n720 := cc 8 [w294,w1,w2,w3,w336,w123,w5] [179,189,466,535,666] [n719] (by decide +kernel)
def n721 := cc 7 [w338,w1,w2,w3,w4,w121] [] [] (by decide +kernel)
def v264 : Closed T 7 := rotateClosed n721 auto1 auto1ok
def n722 := cc 8 [w294,w1,w2,w3,w123,w5,w125] [143,179,189,564,664,666] [v264,n719] (by decide +kernel)
def n723 := cc 7 [w339,w340,w296,w1,w2,w3] [] [] (by decide +kernel)
def v265 : Closed T 7 := rotateClosed n723 auto1 auto1ok
def n724 := cc 8 [w341,w294,w1,w2,w3,w123,w5] [161,581,664,666] [v265] (by decide +kernel)
def n725 := cc 8 [w339,w296,w1,w2,w3,w4,w121] [] [] (by decide +kernel)
def v266 : Closed T 8 := rotateClosed n707 auto1 auto1ok
def v267 : Closed T 8 := rotateClosed n725 auto1 auto1ok
def v268 : Closed T 8 := rotateClosed n717 auto1 auto1ok
def v269 : Closed T 8 := rotateClosed n700 auto1 auto1ok
def n726 := cc 9 [w294,w1,w2,w3,w123,w5] [97,524] [v266,v267,n716,n724,v268,n710,v269,n703,n713,n720,n706,n714,n722] (by decide +kernel)
def n727 := cc 6 [w343,w0,w1,w3,w4] [178,191,512,621] [] (by decide +kernel)
def v270 : Closed T 6 := rotateClosed n727 auto1 auto1ok
def n728 := cc 7 [w0,w1,w344,w3,w9,w5] [103,178,179,535] [v270] (by decide +kernel)
def n729 := cc 8 [w0,w1,w2,w344,w3,w4,w5] [101,192,469,535] [n728] (by decide +kernel)
def v271 : Closed T 7 := rotateClosed n644 auto1 auto1ok
def v272 : Closed T 7 := rotateClosed n674 auto1 auto1ok
def v273 : Closed T 7 := rotateClosed n683 auto1 auto1ok
def n730 := cc 8 [w294,w0,w1,w2,w3,w304,w5] [106,187,254,464,550,607] [v271,v272,v273,n653] (by decide +kernel)
def n731 := cc 7 [w345,w0,w1,w298,w3,w5] [103,179,539] [v270] (by decide +kernel)
def n732 := cc 6 [w0,w346,w1,w3,w4] [178,188,512,618] [] (by decide +kernel)
def n733 := cc 7 [w301,w294,w0,w1,w3,w4] [178,187,512,518,521,617] [n727,n645,n675,n711,n732] (by decide +kernel)
def v274 : Closed T 7 := rotateClosed n646 auto1 auto1ok
def v275 : Closed T 7 := rotateClosed n676 auto1 auto1ok
def v276 : Closed T 7 := rotateClosed n731 auto1 auto1ok
def v277 : Closed T 7 := rotateClosed n663 auto1 auto1ok
def v278 : Closed T 7 := rotateClosed n728 auto1 auto1ok
def n734 := cc 8 [w294,w0,w1,w300,w3,w4,w15] [108,179,187,552,607] [n733,v274,v275,v276,n712,v277,v278] (by decide +kernel)
def v279 : Closed T 8 := rotateClosed n647 auto1 auto1ok
def v280 : Closed T 8 := rotateClosed n677 auto1 auto1ok
def v281 : Closed T 8 := rotateClosed n692 auto1 auto1ok
def v282 : Closed T 8 := rotateClosed n729 auto1 auto1ok
def n735 := cc 9 [w294,w0,w1,w300,w2,w3,w4,w5] [8,104,187,278,287,401,464,607] [v279,v280,n734,n730,n713,v281,v247,v282] (by decide +kernel)
def n736 := cc 8 [w345,w0,w1,w2,w3,w4,w5] [127,197,397,639] [n731] (by decide +kernel)
def v283 : Closed T 8 := rotateClosed n648 auto1 auto1ok
def v284 : Closed T 8 := rotateClosed n678 auto1 auto1ok
def v285 : Closed T 8 := rotateClosed n736 auto1 auto1ok
def n737 := cc 9 [w294,w0,w1,w2,w3,w4,w5,w15] [90,155,179,184,427,459,464,574,607] [v283,v284,v285,n734,n714,v248,n693,n665] (by decide +kernel)
def v286 : Closed T 6 := rotateClosed n732 auto1 auto1ok
def n738 := cc 7 [w179,w0,w347,w1,w3,w5] [154,178,536] [v286] (by decide +kernel)
def v287 : Closed T 7 := rotateClosed n738 auto1 auto1ok
def n739 := cc 8 [w348,w0,w1,w2,w3,w4,w5] [136,178,445,465,589] [v287] (by decide +kernel)
def n740 := cc 7 [w118,w0,w349,w1,w3,w4] [157,179,188,593] [n732] (by decide +kernel)
def n741 := cc 8 [w118,w181,w294,w0,w1,w3,w4] [157,187,373,447,464,607] [n649,n679,n715,n740,v287,n733] (by decide +kernel)
def n742 := cc 9 [w118,w294,w0,w1,w2,w3,w4,w5] [90,136,155,187,464,589,607] [n741,n650,n680,n716,n695,n666,n739] (by decide +kernel)
def n743 := cc 8 [w0,w349,w1,w2,w3,w4,w5] [179,455,464,603] [n740] (by decide +kernel)
def v288 : Closed T 8 := rotateClosed n741 auto1 auto1ok
def v289 : Closed T 8 := rotateClosed n743 auto1 auto1ok
def n744 := cc 9 [w179,w296,w0,w1,w2,w3,w4,w5] [179,184,394,508,535] [v288,n651,n681,n696,n668,v289] (by decide +kernel)
def v290 : Closed T 9 := rotateClosed n744 auto1 auto1ok
def v291 : Closed T 9 := rotateClosed n652 auto1 auto1ok
def v292 : Closed T 9 := rotateClosed n672 auto1 auto1ok
def v293 : Closed T 9 := rotateClosed n682 auto1 auto1ok
def v294 : Closed T 9 := rotateClosed n699 auto1 auto1ok
def v295 : Closed T 9 := rotateClosed n698 auto1 auto1ok
def n745 := cc 10 [w294,w0,w1,w2,w3,w4,w5] [97,184,459,524] [n742,v290,v291,v292,v293,v294,n735,n737,n726,n671,v295,n691,n673,n661,n643] (by decide +kernel)
def n746 := cc 6 [w1,w2,w351,w3,w123,w121,w13] [178,205] [] (by decide +kernel)
def n747 := cc 7 [w1,w2,w351,w3,w4,w123,w5,w121] [218,671,672] [n746] (by decide +kernel)
def n748 := cc 6 [w352,w0,w1,w2,w3,w123,w121] [97] [] (by decide +kernel)
def n749 := cc 7 [w0,w1,w350,w2,w3,w123,w121,w13] [85,92,98,564,669,670] [n748,n746] (by decide +kernel)
def n750 := cc 8 [w0,w1,w350,w2,w3,w4,w123,w5,w121] [218,664,666,671,672] [n749,n747] (by decide +kernel)
def n751 := cc 8 [w0,w1,w2,w3,w123,w121,w13] [143,389,564,671,672,675] [n749] (by decide +kernel)
def n752 := cc 7 [w341,w340,w0,w1,w2,w3] [83,163,671] [] (by decide +kernel)
def n753 := cc 8 [w341,w0,w1,w2,w3,w4,w121] [90,161,671] [n752] (by decide +kernel)
def n754 := cc 8 [w0,w1,w2,w3,w4,w5,w125] [39,83,90,143,179,184,320,420,483] [] (by decide +kernel)
def v296 : Closed T 8 := rotateClosed n753 auto1 auto1ok
def n755 := cc 9 [w0,w1,w2,w3,w4,w123,w5,w121] [97,214,222,315,327,389,459,564,671,672,675] [n753,v296,n750,n754,n751] (by decide +kernel)
def n756 := cc 8 [w0,w1,w2,w3,w4,w353,w121] [90,143,420,517,564,672] [] (by decide +kernel)
def n757 := cc 8 [w126,w0,w1,w2,w3,w121,w13] [143,517,564,664,672] [] (by decide +kernel)
def n758 := cc 8 [w341,w128,w0,w1,w2,w3,w4] [636,666,669] [] (by decide +kernel)
def v297 : Closed T 8 := rotateClosed n758 auto1 auto1ok
def n759 := cc 9 [w126,w0,w1,w2,w3,w4,w5,w121] [97,222,254,459,564,664,671,672] [v297,n757,n754,n756] (by decide +kernel)
def n760 := cc 6 [w1,w273,w2,w3,w123,w354,w13] [178,205] [] (by decide +kernel)
def n761 := cc 6 [w356,w1,w273,w2,w3,w4,w121] [] [] (by decide +kernel)
def v298 : Closed T 6 := rotateClosed n761 auto1 auto1ok
def n762 := cc 7 [w1,w273,w2,w3,w4,w123,w5,w354] [221,410] [v298,n760] (by decide +kernel)
def v299 : Closed T 6 := rotateClosed n760 auto1 auto1ok
def n763 := cc 7 [w1,w273,w2,w3,w4,w121,w13] [178,223,407,623,662,670] [v299] (by decide +kernel)
def n764 := cc 6 [w357,w273,w2,w3,w4,w5,w125] [218] [] (by decide +kernel)
def n765 := cc 6 [w358,w1,w273,w3,w4,w5,w125] [144] [] (by decide +kernel)
def n766 := cc 7 [w1,w273,w2,w3,w4,w5,w125] [13,218,662,669,670] [n765,n764] (by decide +kernel)
def n767 := cc 7 [w1,w273,w2,w3,w4,w123,w5,w125] [177,214,414,669,671,680] [] (by decide +kernel)
def n768 := cc 7 [w341,w1,w273,w2,w3,w4,w5] [13,143,192,220,669] [] (by decide +kernel)
def v300 : Closed T 7 := rotateClosed n763 auto1 auto1ok
def n769 := cc 8 [w1,w273,w2,w3,w4,w123,w5] [178,214,298,405,474,541,669] [n768,n762,n767,n766,v300] (by decide +kernel)
def n770 := cc 8 [w0,w1,w2,w3,w4,w121,w359] [15,136,222,664] [] (by decide +kernel)
def n771 := cc 8 [w0,w1,w2,w3,w4,w355,w5] [83,90,127,214,303,405,459,541] [] (by decide +kernel)
def n772 := cc 8 [w360,w0,w1,w2,w3,w4,w5] [0,214,269,675] [] (by decide +kernel)
def n773 := cc 7 [w361,w0,w1,w2,w3,w4,w121] [104,132,146,625,662] [] (by decide +kernel)
def n774 := cc 8 [w0,w272,w1,w2,w3,w4,w121,w13] [90,143,223,329,420,622,670,676,684] [n773,n763] (by decide +kernel)
def n775 := cc 7 [w362,w0,w1,w2,w3,w4,w5] [11,12,132,135,146,167,170,172,269] [] (by decide +kernel)
def n776 := cc 7 [w362,w0,w1,w2,w3,w4,w5,w125] [83,90,144,662] [] (by decide +kernel)
def n777 := cc 7 [w0,w272,w357,w2,w3,w4,w5,w125] [83,90,218,423,671] [n764] (by decide +kernel)
def n778 := cc 6 [w358,w363,w0,w1,w3,w4,w5] [] [] (by decide +kernel)
def n779 := cc 7 [w358,w0,w272,w1,w3,w4,w5] [179,218,422,484] [n778] (by decide +kernel)
def n780 := cc 7 [w358,w0,w272,w1,w3,w4,w5,w125] [83,90,218,423] [n765] (by decide +kernel)
def n781 := cc 8 [w0,w272,w1,w2,w3,w4,w5,w125] [39,83,90,143,218,267,320,420,483,669,670,684] [n779,n780,n775,n776,n777,n766] (by decide +kernel)
def n782 := cc 7 [w362,w0,w1,w2,w3,w4,w123,w5] [101,135,146,165,172,414] [] (by decide +kernel)
def n783 := cc 8 [w0,w272,w1,w2,w3,w4,w123,w5,w125] [83,143,177,214,452,483,664,669,671,680] [n782,n767] (by decide +kernel)
def n784 := cc 8 [w341,w0,w272,w1,w2,w3,w4,w5] [10,41,220,325,483,666,669] [n768] (by decide +kernel)
def v301 : Closed T 8 := rotateClosed n774 auto1 auto1ok
def v302 : Closed T 8 := rotateClosed n770 auto1 auto1ok
def n785 := cc 9 [w0,w272,w1,w2,w3,w4,w123,w5] [83,97,214,315,389,483,540,669,675] [n784,n772,n783,n781,v301,n771,v302,n769] (by decide +kernel)
def n786 := cc 8 [w364,w0,w1,w2,w3,w4,w5] [0,179,269,431,521] [] (by decide +kernel)
def n787 := cc 8 [w39,w0,w1,w2,w3,w4,w121,w13] [223,517,648,672,684] [] (by decide +kernel)
def n788 := cc 8 [w39,w0,w1,w2,w3,w4,w5,w125] [66,218,269,670,671,684] [] (by decide +kernel)
def v303 : Closed T 8 := rotateClosed n787 auto1 auto1ok
def n789 := cc 9 [w39,w0,w1,w2,w3,w4,w123,w5] [97,214,315,459,585,671] [v10,n786,n788,v303] (by decide +kernel)
def n790 := cc 6 [w1,w136,w145,w3,w4,w121,w15] [182,288] [] (by decide +kernel)
def n791 := cc 6 [w365,w1,w136,w2,w3,w4,w121] [] [] (by decide +kernel)
def v304 : Closed T 6 := rotateClosed n791 auto1 auto1ok
def v305 : Closed T 6 := rotateClosed n790 auto1 auto1ok
def n792 := cc 7 [w1,w136,w2,w145,w3,w4,w123,w5] [22,209,381,409,415] [v304,v305] (by decide +kernel)
def n793 := cc 6 [w1,w136,w2,w3,w123,w137,w13] [182,291] [] (by decide +kernel)
def n794 := cc 6 [w366,w1,w136,w2,w3,w4,w121] [] [] (by decide +kernel)
def v306 : Closed T 6 := rotateClosed n794 auto1 auto1ok
def n795 := cc 7 [w1,w136,w2,w3,w4,w123,w5,w137] [326,418] [v306,n793] (by decide +kernel)
def n796 := cc 6 [w1,w136,w2,w3,w4,w15,w125] [] [] (by decide +kernel)
def n797 := cc 6 [w341,w1,w136,w2,w3,w9,w5] [] [] (by decide +kernel)
def n798 := cc 6 [w1,w136,w2,w3,w4,w121,w44] [182] [] (by decide +kernel)
def n799 := cc 6 [w46,w1,w136,w2,w3,w123,w5] [] [] (by decide +kernel)
def v307 : Closed T 6 := rotateClosed n797 auto1 auto1ok
def v308 : Closed T 6 := rotateClosed n799 auto1 auto1ok
def n800 := cc 7 [w1,w136,w2,w3,w4,w121,w15] [182,210,518,670] [v307,v308,n798,n796,n790] (by decide +kernel)
def n801 := cc 7 [w1,w136,w2,w3,w4,w123,w119,w5] [152,315,449,669,680] [] (by decide +kernel)
def n802 := cc 6 [w1,w136,w2,w3,w4,w367,w5] [] [] (by decide +kernel)
def n803 := cc 6 [w124,w1,w136,w2,w3,w5,w13] [] [] (by decide +kernel)
def v309 : Closed T 6 := rotateClosed n802 auto1 auto1ok
def n804 := cc 7 [w124,w1,w136,w2,w3,w4,w5] [127,272,669] [n803,v309] (by decide +kernel)
def n805 := cc 6 [w1,w136,w2,w3,w123,w15,w13] [] [] (by decide +kernel)
def v310 : Closed T 6 := rotateClosed n798 auto1 auto1ok
def n806 := cc 7 [w1,w136,w2,w3,w4,w123,w5,w15] [209,427,669] [n225,v310,n796,n805] (by decide +kernel)
def n807 := cc 6 [w47,w1,w136,w2,w3,w4,w121] [] [] (by decide +kernel)
def v311 : Closed T 6 := rotateClosed n803 auto1 auto1ok
def v312 : Closed T 6 := rotateClosed n793 auto1 auto1ok
def v313 : Closed T 6 := rotateClosed n805 auto1 auto1ok
def n808 := cc 7 [w1,w136,w2,w3,w4,w121,w13] [23,182,417,662,670] [v311,n807,n798,n224,v312,v313] (by decide +kernel)
def n809 := cc 6 [w357,w136,w2,w3,w4,w5,w125] [320,566] [] (by decide +kernel)
def n810 := cc 6 [w358,w1,w136,w2,w3,w4,w5] [] [] (by decide +kernel)
def v314 : Closed T 6 := rotateClosed n796 auto1 auto1ok
def n811 := cc 7 [w1,w136,w2,w3,w4,w5,w125] [267,320,481,555,662,669,670] [n810,n809,n225,n796,v314] (by decide +kernel)
def n812 := cc 7 [w1,w136,w2,w3,w4,w123,w5,w125] [177,315,419,669,680] [] (by decide +kernel)
def n813 := cc 6 [w1,w136,w2,w368,w3,w4,w5] [269] [] (by decide +kernel)
def n814 := cc 7 [w341,w1,w136,w2,w3,w4,w5] [143,281,669] [n797,n813] (by decide +kernel)
def v315 : Closed T 7 := rotateClosed n800 auto1 auto1ok
def v316 : Closed T 7 := rotateClosed n808 auto1 auto1ok
def n815 := cc 8 [w1,w136,w2,w3,w4,w123,w5] [22,182,209,415,481,669] [n814,n804,n792,n801,n795,n806,n812,n227,n811,v315,v316] (by decide +kernel)
def n816 := cc 7 [w124,w0,w1,w2,w3,w43,w5] [168,269,666] [] (by decide +kernel)
def v317 : Closed T 7 := rotateClosed n816 auto1 auto1ok
def n817 := cc 8 [w0,w1,w2,w3,w4,w121,w369] [142,179,327,664] [v317] (by decide +kernel)
def n818 := cc 8 [w0,w1,w2,w3,w4,w138,w5] [138,179,184,315,415,666] [] (by decide +kernel)
def n819 := cc 8 [w370,w0,w1,w2,w3,w4,w5] [315,671,675] [] (by decide +kernel)
def n820 := cc 6 [w147,w0,w1,w2,w3,w5,w125] [] [] (by decide +kernel)
def n821 := cc 6 [w341,w147,w0,w1,w2,w3,w5] [] [] (by decide +kernel)
def n822 := cc 7 [w147,w0,w1,w2,w3,w123,w5] [92,110,133,512] [n821,n820] (by decide +kernel)
def n823 := cc 6 [w371,w0,w1,w2,w3,w4,w15] [184] [] (by decide +kernel)
def v318 : Closed T 6 := rotateClosed n820 auto1 auto1ok
def n824 := cc 7 [w0,w41,w1,w2,w3,w4,w15,w125] [86,180,218,421] [v318,n823,n796] (by decide +kernel)
def n825 := cc 7 [w341,w0,w41,w1,w2,w3,w9,w5] [93,181,220,666] [n821,n797] (by decide +kernel)
def n826 := cc 6 [w149,w0,w1,w2,w3,w4,w121] [97] [] (by decide +kernel)
def n827 := cc 7 [w0,w41,w1,w2,w3,w4,w121,w44] [85,90,132,223,421,672] [n826,n798] (by decide +kernel)
def n828 := cc 7 [w46,w0,w41,w1,w2,w3,w123,w5] [83,92,249,522,671] [n799] (by decide +kernel)
def v319 : Closed T 7 := rotateClosed n825 auto1 auto1ok
def v320 : Closed T 7 := rotateClosed n828 auto1 auto1ok
def v321 : Closed T 7 := rotateClosed n822 auto1 auto1ok
def n829 := cc 8 [w0,w41,w1,w2,w3,w4,w121,w15] [90,136,222,328,421,670,672,676,679,686] [v319,v320,v321,n827,n824,n800] (by decide +kernel)
def n830 := cc 7 [w150,w0,w1,w2,w3,w4,w123,w5] [37,40,133,149,150,449] [] (by decide +kernel)
def n831 := cc 8 [w0,w41,w1,w2,w3,w4,w123,w119,w5] [83,127,152,179,214,315,448,669,680] [n830,n801] (by decide +kernel)
def n832 := cc 6 [w0,w1,w372,w2,w3,w5,w13] [459] [] (by decide +kernel)
def n833 := cc 7 [w0,w1,w372,w2,w3,w4,w5] [0,90,166,211,432,459] [n832] (by decide +kernel)
def n834 := cc 7 [w0,w41,w1,w2,w3,w4,w367,w5] [83,172,492,517,664] [n802] (by decide +kernel)
def n835 := cc 6 [w124,w148,w0,w1,w2,w3,w5] [] [] (by decide +kernel)
def n836 := cc 7 [w124,w0,w41,w1,w2,w3,w5,w13] [53,484,675] [n835,n803,n832] (by decide +kernel)
def v322 : Closed T 7 := rotateClosed n834 auto1 auto1ok
def n837 := cc 8 [w124,w0,w41,w1,w2,w3,w4,w5] [0,214,324,484,669,675] [n836,n816,n804,v322,n833] (by decide +kernel)
def n838 := cc 6 [w147,w0,w1,w2,w3,w121,w13] [512] [] (by decide +kernel)
def n839 := cc 7 [w147,w0,w1,w2,w3,w4,w5,w121] [90,443,670] [n820,n838] (by decide +kernel)
def n840 := cc 6 [w148,w0,w1,w2,w3,w123,w15] [] [] (by decide +kernel)
def v323 : Closed T 6 := rotateClosed n838 auto1 auto1ok
def n841 := cc 7 [w0,w41,w1,w2,w3,w123,w15,w13] [86,217,669,671,680] [v323,n840,n805] (by decide +kernel)
def v324 : Closed T 7 := rotateClosed n839 auto1 auto1ok
def v325 : Closed T 7 := rotateClosed n827 auto1 auto1ok
def n842 := cc 8 [w0,w41,w1,w2,w3,w4,w123,w5,w15] [136,214,315,483,664,666,669,671,679,680] [v324,n261,v325,n824,n841,n806] (by decide +kernel)
def v326 : Closed T 6 := rotateClosed n835 auto1 auto1ok
def v327 : Closed T 6 := rotateClosed n840 auto1 auto1ok
def n843 := cc 7 [w148,w0,w1,w2,w3,w4,w121] [113,147,179,662] [v326,n256,v327] (by decide +kernel)
def n844 := cc 6 [w0,w1,w48,w2,w3,w4,w121] [] [] (by decide +kernel)
def n845 := cc 7 [w47,w0,w41,w1,w2,w3,w4,w121] [90,457,672,676] [n807,n844] (by decide +kernel)
def v328 : Closed T 7 := rotateClosed n836 auto1 auto1ok
def v329 : Closed T 7 := rotateClosed n841 auto1 auto1ok
def n846 := cc 8 [w0,w41,w1,w2,w3,w4,w121,w13] [90,143,223,329,564,670,671,676,687] [v328,n845,n843,n827,n257,v329,n808] (by decide +kernel)
def v330 : Closed T 6 := rotateClosed n823 auto1 auto1ok
def n847 := cc 7 [w371,w0,w1,w2,w3,w4,w5] [147,179,184,320,485,569] [n823,v330] (by decide +kernel)
def n848 := cc 7 [w371,w0,w1,w2,w3,w4,w5,w125] [83,90,145,662] [] (by decide +kernel)
def n849 := cc 7 [w0,w41,w357,w2,w3,w4,w5,w125] [83,320,323,565] [n809] (by decide +kernel)
def n850 := cc 6 [w0,w1,w373,w2,w3,w4,w5] [83] [] (by decide +kernel)
def n851 := cc 7 [w358,w0,w41,w1,w2,w3,w4,w5] [0,83,90,179,218,269,422,484] [n810,n850] (by decide +kernel)
def v331 : Closed T 7 := rotateClosed n824 auto1 auto1ok
def n852 := cc 8 [w0,w41,w1,w2,w3,w4,w5,w125] [83,90,143,218,267,320,483,564,669,670,671,684] [n851,n847,n848,n849,n261,n824,v331,n811] (by decide +kernel)
def n853 := cc 7 [w371,w0,w1,w2,w3,w4,w123,w5] [37,40,141,147,175,419] [] (by decide +kernel)
def n854 := cc 8 [w0,w41,w1,w2,w3,w4,w123,w5,w125] [83,143,177,315,452,483,664,669,680] [n853,n812] (by decide +kernel)
def n855 := cc 6 [w374,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n856 := cc 7 [w0,w41,w1,w2,w368,w3,w4,w5] [0,179,220,269,439,666] [n855,n813] (by decide +kernel)
def n857 := cc 8 [w341,w0,w41,w1,w2,w3,w4,w5] [220,325,483,666,669,671] [n825,n814,n856] (by decide +kernel)
def v332 : Closed T 8 := rotateClosed n829 auto1 auto1ok
def v333 : Closed T 8 := rotateClosed n846 auto1 auto1ok
def v334 : Closed T 8 := rotateClosed n817 auto1 auto1ok
def n858 := cc 9 [w0,w41,w1,w2,w3,w4,w123,w5] [83,97,214,315,389,483,669,671,675] [n857,n837,n819,n831,n842,n854,n263,n852,v332,v333,n818,v334,n815] (by decide +kernel)
def n859 := cc 8 [w0,w1,w2,w376,w3,w4,w5] [127,152,269,521,526] [] (by decide +kernel)
def n860 := cc 8 [w0,w1,w2,w3,w4,w377,w5] [83,143,179,218,320,420,483,565] [] (by decide +kernel)
def n861 := cc 8 [w378,w0,w1,w2,w3,w4,w5] [90,161,179,220,325,438,528] [] (by decide +kernel)
def n862 := cc 8 [w0,w375,w1,w2,w3,w5,w13] [83,143,217,319,483,521,525,671] [] (by decide +kernel)
def v335 : Closed T 8 := rotateClosed n32 auto1 auto1ok
def v336 : Closed T 8 := rotateClosed n860 auto1 auto1ok
def n863 := cc 9 [w0,w375,w1,w2,w3,w4,w5] [97,214,315,389,483,525,671,675] [v335,n861,n786,n862,n859,v336] (by decide +kernel)
def n864 := cc 9 [w0,w375,w1,w2,w3,w4,w123,w5] [97,315,525,671,675] [v335] (by decide +kernel)
def n865 := cc 9 [w34,w0,w1,w2,w3,w4,w5,w121] [97,222,327,459,653,664,670] [n32] (by decide +kernel)
def n866 := cc 7 [w1,w156,w2,w3,w121,w13] [420,564,664,671] [] (by decide +kernel)
def n867 := cc 8 [w1,w156,w2,w3,w4,w5,w121] [483,564,664,671] [n866] (by decide +kernel)
def n868 := cc 8 [w0,w1,w2,w3,w4,w121,w379] [90,143,179,420,517,564] [] (by decide +kernel)
def n869 := cc 8 [w0,w1,w2,w3,w4,w380,w5] [83,143,179,218,320,420,483,546] [] (by decide +kernel)
def n870 := cc 8 [w381,w0,w1,w2,w3,w4,w5] [161,179,220,325,438,548,666] [] (by decide +kernel)
def n871 := cc 8 [w0,w155,w1,w2,w3,w121,w13] [143,517,564,664,672] [n866] (by decide +kernel)
def v337 : Closed T 8 := rotateClosed n870 auto1 auto1ok
def v338 : Closed T 8 := rotateClosed n869 auto1 auto1ok
def n872 := cc 9 [w0,w155,w1,w2,w3,w4,w5,w121] [97,222,459,517,564,664,672] [v337,n871,v338,n868,n867] (by decide +kernel)
def n873 := cc 8 [w49,w0,w1,w2,w3,w123,w9,w5] [38,127,214,316,666] [] (by decide +kernel)
def n874 := cc 8 [w49,w0,w1,w2,w3,w123,w13] [319,483,587,675] [n287] (by decide +kernel)
def n875 := cc 9 [w49,w0,w1,w2,w3,w4,w123,w5] [97,214,315,483,587,675] [n35,n861,n288,n873,n874] (by decide +kernel)
def n876 := cc 6 [w1,w2,w351,w3,w123,w382,w13] [178,205] [] (by decide +kernel)
def n877 := cc 6 [w384,w1,w2,w351,w3,w4,w121] [] [] (by decide +kernel)
def v339 : Closed T 6 := rotateClosed n877 auto1 auto1ok
def n878 := cc 7 [w1,w2,w351,w3,w4,w123,w5,w382] [221,561] [v339,n876] (by decide +kernel)
def v340 : Closed T 6 := rotateClosed n876 auto1 auto1ok
def n879 := cc 7 [w1,w2,w351,w3,w4,w121,w13] [178,223,559,662,672] [v340] (by decide +kernel)
def n880 := cc 6 [w358,w1,w351,w3,w4,w5,w125] [184,572] [] (by decide +kernel)
def n881 := cc 7 [w1,w2,w351,w3,w4,w5,w125] [218,320,559,662,671,672] [n880] (by decide +kernel)
def n882 := cc 7 [w1,w2,w351,w3,w4,w123,w5,w125] [214,315,563,671,672] [] (by decide +kernel)
def n883 := cc 7 [w341,w1,w2,w351,w3,w4,w5] [192,218,220,269,671] [] (by decide +kernel)
def v341 : Closed T 7 := rotateClosed n879 auto1 auto1ok
def n884 := cc 8 [w1,w2,w351,w3,w4,w123,w5] [178,214,556,634,671] [n883,n878,n882,n881,v341] (by decide +kernel)
def n885 := cc 7 [w0,w1,w2,w351,w3,w4,w121,w13] [85,178,223,260,559] [n746] (by decide +kernel)
def n886 := cc 7 [w0,w1,w2,w351,w3,w4,w5,w125] [26,179,218,233,269] [] (by decide +kernel)
def v342 : Closed T 7 := rotateClosed n885 auto1 auto1ok
def n887 := cc 8 [w0,w1,w2,w351,w3,w4,w123,w5] [178,315,634,664,671] [n886,v342,n747] (by decide +kernel)
def n888 := cc 8 [w0,w1,w2,w3,w4,w121,w385] [97,222,258,327,664] [] (by decide +kernel)
def n889 := cc 8 [w0,w1,w2,w3,w4,w383,w5] [214,254,315,666] [] (by decide +kernel)
def n890 := cc 8 [w386,w0,w1,w2,w3,w4,w5] [214,315,675] [] (by decide +kernel)
def n891 := cc 7 [w352,w0,w1,w2,w3,w4,w121] [99,223,662] [n748] (by decide +kernel)
def n892 := cc 8 [w0,w1,w350,w2,w3,w4,w121,w13] [90,98,223,564,672,676,687] [n891,n749,n885,n879] (by decide +kernel)
def n893 := cc 7 [w387,w0,w1,w2,w3,w4,w5] [0,218,220,224,233,269] [] (by decide +kernel)
def n894 := cc 7 [w387,w0,w1,w2,w3,w4,w5,w125] [83,90,218,662] [] (by decide +kernel)
def n895 := cc 7 [w358,w0,w1,w350,w3,w4,w5] [179,218,570,637] [] (by decide +kernel)
def n896 := cc 7 [w358,w0,w1,w350,w3,w4,w5,w125] [83,90,184,570,571] [n880] (by decide +kernel)
def n897 := cc 8 [w0,w1,w350,w2,w3,w4,w5,w125] [83,90,143,218,320,564,636,671,672,687] [n895,n896,n893,n894,n886,n881] (by decide +kernel)
def n898 := cc 7 [w387,w0,w1,w2,w3,w4,w123,w5] [83,218,563,570] [] (by decide +kernel)
def n899 := cc 8 [w0,w1,w350,w2,w3,w4,w123,w5,w125] [83,221,315,483,564,601,664,671,672] [n898,n882] (by decide +kernel)
def n900 := cc 8 [w341,w0,w1,w350,w2,w3,w4,w5] [325,636,666,671] [n883] (by decide +kernel)
def v343 : Closed T 8 := rotateClosed n892 auto1 auto1ok
def v344 : Closed T 8 := rotateClosed n888 auto1 auto1ok
def n901 := cc 9 [w0,w1,w350,w2,w3,w4,w123,w5] [83,97,98,214,524,636,671,675] [n900,n890,n750,n899,n897,v343,n887,n889,v344,n884] (by decide +kernel)
def n902 := cc 8 [w0,w1,w2,w3,w4,w388,w5] [101,179,315,383,666] [] (by decide +kernel)
def n903 := cc 8 [w0,w1,w2,w389,w3,w4,w5] [315,511,675] [] (by decide +kernel)
def n904 := cc 8 [w164,w0,w1,w2,w3,w4,w121,w13] [90,329,564,672,676,687] [] (by decide +kernel)
def n905 := cc 7 [w0,w1,w2,w390,w3,w4,w5,w125] [269] [] (by decide +kernel)
def n906 := cc 7 [w164,w0,w1,w391,w3,w4,w5,w125] [83,570] [] (by decide +kernel)
def n907 := cc 8 [w164,w0,w1,w2,w3,w4,w5,w125] [83,320,511,671,672,687] [n906,n905] (by decide +kernel)
def v345 : Closed T 8 := rotateClosed n904 auto1 auto1ok
def n908 := cc 9 [w164,w0,w1,w2,w3,w4,w123,w5] [315,524,636,671,675] [n907,v345,n903,n902] (by decide +kernel)
def n909 := cc 8 [w166,w1,w2,w3,w123,w9,w5] [127,179,512,666] [] (by decide +kernel)
def n910 := cc 8 [w167,w1,w2,w3,w123,w9,w5] [97,666,678] [] (by decide +kernel)
def n911 := cc 8 [w0,w168,w1,w2,w3,w123,w9,w5] [127,666,685] [] (by decide +kernel)
def n912 := cc 8 [w0,w1,w329,w3,w123,w9,w5] [666,669] [] (by decide +kernel)
def n913 := cc 8 [w124,w0,w1,w3,w123,w9,w5] [184,666,669] [] (by decide +kernel)
def n914 := cc 8 [w65,w0,w1,w2,w3,w123,w9,w5] [159,245,316,666,672] [] (by decide +kernel)
def n915 := cc 8 [w0,w1,w2,w172,w3,w123,w9,w5] [179,316,512,666] [] (by decide +kernel)
def n916 := cc 8 [w0,w1,w2,w3,w4,w15,w125] [90,137,184,568,671] [n824] (by decide +kernel)
def n917 := cc 8 [w341,w0,w1,w2,w3,w9,w5] [162,581,666,671] [n825] (by decide +kernel)
def n918 := cc 8 [w0,w1,w2,w3,w4,w121,w44] [97,132,179,568,664] [n827] (by decide +kernel)
def n919 := cc 8 [w46,w0,w1,w2,w3,w123,w5] [134,589,666,672] [n828] (by decide +kernel)
def v346 : Closed T 8 := rotateClosed n873 auto1 auto1ok
def v347 : Closed T 8 := rotateClosed n914 auto1 auto1ok
def v348 : Closed T 8 := rotateClosed n917 auto1 auto1ok
def v349 : Closed T 8 := rotateClosed n919 auto1 auto1ok
def v350 : Closed T 8 := rotateClosed n913 auto1 auto1ok
def v351 : Closed T 8 := rotateClosed n910 auto1 auto1ok
def v352 : Closed T 8 := rotateClosed n909 auto1 auto1ok
def v353 : Closed T 8 := rotateClosed n911 auto1 auto1ok
def v354 : Closed T 8 := rotateClosed n912 auto1 auto1ok
def v355 : Closed T 8 := rotateClosed n915 auto1 auto1ok
def n920 := cc 9 [w0,w1,w2,w3,w4,w121,w15] [97,136,184,222,607,664,671,672] [v346,v347,v348,v349,v350,n509,n618,v351,v352,n829,v353,v354,v355,n918,n916,n187] (by decide +kernel)
def n921 := cc 8 [w167,w1,w2,w3,w4,w123,w5] [83,448,512,597] [n345] (by decide +kernel)
def n922 := cc 8 [w124,w0,w1,w3,w4,w9,w5] [83,179,431,577] [n345] (by decide +kernel)
def n923 := cc 9 [w0,w1,w2,w3,w4,w123,w9,w5] [97,184,389,524,666,671] [n922,n921,n191] (by decide +kernel)
def n924 := cc 8 [w292,w1,w2,w3,w4,w5,w121] [90,222,521,632] [] (by decide +kernel)
def n925 := cc 8 [w0,w1,w2,w3,w4,w121,w15] [136,222,664] [] (by decide +kernel)
def n926 := cc 8 [w118,w122,w0,w1,w3,w4,w5] [222,521,641,664] [] (by decide +kernel)
def n927 := cc 9 [w118,w0,w1,w2,w3,w4,w5,w121] [97,222,459,664,672] [n926,v131,n925,n924] (by decide +kernel)
def n928 := cc 8 [w0,w1,w392,w2,w3,w123,w5] [101,178,675] [] (by decide +kernel)
def n929 := cc 8 [w0,w1,w2,w3,w4,w393,w121] [459,607,670,671] [] (by decide +kernel)
def n930 := cc 8 [w179,w0,w1,w2,w3,w5,w125] [83,169,180,218,452,564,664] [] (by decide +kernel)
def n931 := cc 8 [w341,w179,w0,w1,w2,w3,w5] [184,581,664,666,669] [] (by decide +kernel)
def v356 : Closed T 8 := rotateClosed n929 auto1 auto1ok
def v357 : Closed T 8 := rotateClosed n925 auto1 auto1ok
def n932 := cc 9 [w179,w0,w1,w2,w3,w123,w5] [97,214,389,524,672,675] [n931,n930,n928,v356,v357] (by decide +kernel)
def n933 := cc 8 [w0,w1,w2,w3,w4,w123,w330] [214,673,675] [n701] (by decide +kernel)
def n934 := cc 8 [w332,w0,w1,w2,w3,w5,w121] [109,222,463,564] [] (by decide +kernel)
def n935 := cc 7 [w394,w0,w1,w3,w4,w5] [222,664,672] [] (by decide +kernel)
def v358 : Closed T 7 := rotateClosed n935 auto1 auto1ok
def n936 := cc 8 [w0,w1,w329,w3,w4,w119,w5] [666,669] [v358] (by decide +kernel)
def v359 : Closed T 8 := rotateClosed n934 auto1 auto1ok
def n937 := cc 9 [w0,w1,w329,w2,w3,w4,w123,w5] [97,214,389,673,675] [v359,n349,n703,n936,n912,n933] (by decide +kernel)
def n938 := cc 8 [w0,w140,w1,w2,w3,w4,w123,w5] [214,666,680] [] (by decide +kernel)
def n939 := cc 9 [w0,w1,w2,w3,w4,w123,w119,w5] [214,315,556,666,671] [v76,n350,n921,n706,n831,n938,n936] (by decide +kernel)
def n940 := cc 8 [w334,w122,w0,w1,w3,w4,w5] [664,670] [n935] (by decide +kernel)
def n941 := cc 9 [w334,w0,w1,w2,w3,w4,w5,w121] [222,664,672] [n940,v131,n492,n924] (by decide +kernel)
def n942 := cc 8 [w0,w395,w1,w2,w3,w4,w5] [171,222,680] [] (by decide +kernel)
def n943 := cc 8 [w0,w1,w2,w3,w4,w367,w5] [83,492,642,671] [n834] (by decide +kernel)
def n944 := cc 8 [w396,w0,w1,w2,w3,w4,w5] [0,90,179,269,669] [] (by decide +kernel)
def n945 := cc 8 [w124,w0,w1,w2,w3,w5,w13] [169,459,577,672,675,682] [n836] (by decide +kernel)
def n946 := cc 8 [w70,w124,w0,w1,w2,w3,w5] [73,521,669] [] (by decide +kernel)
def v360 : Closed T 8 := rotateClosed n926 auto1 auto1ok
def v361 : Closed T 8 := rotateClosed n942 auto1 auto1ok
def v362 : Closed T 8 := rotateClosed n943 auto1 auto1ok
def n947 := cc 9 [w124,w0,w1,w2,w3,w4,w5] [97,214,269,389,459,577,669,672,673,675] [n944,v360,n946,n786,n510,n837,n945,n189,n922,n350,v361,v362,n191] (by decide +kernel)
def v363 : Closed T 8 := rotateClosed n940 auto1 auto1ok
def n948 := cc 9 [w124,w0,w1,w2,w3,w4,w123,w5] [83,97,179,214,389,669,673,675] [v363,n710,n350,n913] (by decide +kernel)
def n949 := cc 8 [w0,w1,w2,w3,w4,w121,w299] [90,97,222,258,564] [] (by decide +kernel)
def n950 := cc 8 [w0,w1,w2,w3,w4,w397,w5] [83,106,214,254,636] [] (by decide +kernel)
def n951 := cc 8 [w398,w0,w1,w2,w3,w4,w5] [109,214,404,636] [] (by decide +kernel)
def n952 := cc 7 [w301,w0,w1,w3,w4,w123] [214,636,666,671] [n711] (by decide +kernel)
def v364 : Closed T 7 := rotateClosed n952 auto1 auto1ok
def n953 := cc 8 [w0,w1,w298,w3,w9,w5,w121] [222,564,672] [v364] (by decide +kernel)
def v365 : Closed T 8 := rotateClosed n951 auto1 auto1ok
def v366 : Closed T 8 := rotateClosed n950 auto1 auto1ok
def n954 := cc 9 [w0,w1,w298,w2,w3,w4,w5,w121] [222,459,564,675] [v365,n953,v366,n949] (by decide +kernel)
def n955 := cc 6 [w400,w1,w399,w2,w3,w4,w121] [] [] (by decide +kernel)
def n956 := cc 6 [w1,w399,w2,w3,w121,w13] [477,682] [] (by decide +kernel)
def n957 := cc 7 [w1,w399,w2,w3,w4,w5,w121] [127,216,407,682] [n955,n956] (by decide +kernel)
def n958 := cc 7 [w0,w168,w1,w2,w3,w121,w13] [672,676,682] [n956] (by decide +kernel)
def n959 := cc 8 [w0,w168,w1,w2,w3,w4,w5,w121] [90,420,672,682] [n958,n957] (by decide +kernel)
def n960 := cc 7 [w0,w1,w2,w3,w401,w13] [452,518,669,673] [] (by decide +kernel)
def v367 : Closed T 7 := rotateClosed n958 auto1 auto1ok
def n961 := cc 8 [w0,w1,w2,w3,w123,w15,w13] [137,574,671,675] [v16,n841,v367,n960] (by decide +kernel)
def n962 := cc 8 [w0,w1,w2,w3,w4,w401,w5] [0,97,184,269,518,669] [n960] (by decide +kernel)
def n963 := cc 8 [w402,w0,w1,w2,w3,w4,w5] [672,678] [] (by decide +kernel)
def v368 : Closed T 8 := rotateClosed n37 auto1 auto1ok
def v369 : Closed T 8 := rotateClosed n963 auto1 auto1ok
def v370 : Closed T 8 := rotateClosed n959 auto1 auto1ok
def v371 : Closed T 8 := rotateClosed n953 auto1 auto1ok
def v372 : Closed T 8 := rotateClosed n918 auto1 auto1ok
def n964 := cc 9 [w0,w1,w2,w3,w4,w123,w5,w15] [136,315,345,389,459,574,671,675] [n944,v368,v369,n714,n842,v370,v371,n962,n357,v372,n916,n961] (by decide +kernel)
def n965 := cc 8 [w0,w1,w2,w3,w4,w403,w121] [90,222,671] [] (by decide +kernel)
def n966 := cc 8 [w0,w1,w2,w3,w4,w404,w5] [0,83,214,269,672] [] (by decide +kernel)
def n967 := cc 8 [w0,w1,w2,w3,w4,w405,w5] [0,269,517,670] [] (by decide +kernel)
def n968 := cc 8 [w118,w181,w0,w1,w3,w4,w123] [157,214,447,636] [n715,n952] (by decide +kernel)
def v373 : Closed T 8 := rotateClosed n967 auto1 auto1ok
def v374 : Closed T 8 := rotateClosed n965 auto1 auto1ok
def n969 := cc 9 [w118,w0,w1,w2,w3,w4,w123,w5] [214,315,369,389,589,675] [n968,n716,v373,n966,v374] (by decide +kernel)
def n970 := cc 8 [w0,w1,w2,w3,w4,w406,w121] [81,420,672] [] (by decide +kernel)
def n971 := cc 8 [w0,w1,w2,w3,w4,w407,w5] [83,101,179,483,505,636] [] (by decide +kernel)
def n972 := cc 8 [w0,w1,w408,w2,w3,w4,w5] [636,666,669] [] (by decide +kernel)
def n973 := cc 8 [w179,w0,w1,w2,w3,w121,w13] [42,420,664,672] [] (by decide +kernel)
def v375 : Closed T 8 := rotateClosed n968 auto1 auto1ok
def v376 : Closed T 8 := rotateClosed n972 auto1 auto1ok
def v377 : Closed T 8 := rotateClosed n971 auto1 auto1ok
def n974 := cc 9 [w179,w0,w1,w2,w3,w4,w5,w121] [420,459,564,672] [v375,n930,n973,v376,v377,n970] (by decide +kernel)
def n975 := cc 9 [w0,w1,w2,w409,w3,w4,w123,w5] [315,524,671,675] [] (by decide +kernel)
def n976 := cc 9 [w410,w0,w1,w2,w3,w4,w5,w121] [327,607,664,674] [n609] (by decide +kernel)
def n977 := cc 8 [w0,w1,w2,w3,w4,w121,w61] [90,199,327,385,420,671] [] (by decide +kernel)
def n978 := cc 8 [w0,w1,w2,w3,w4,w411,w5] [83,184,383,483,564,672] [] (by decide +kernel)
def n979 := cc 8 [w412,w0,w1,w2,w3,w4,w5] [315,666,669] [] (by decide +kernel)
def v378 : Closed T 8 := rotateClosed n979 auto1 auto1ok
def v379 : Closed T 8 := rotateClosed n978 auto1 auto1ok
def n980 := cc 9 [w0,w1,w2,w60,w3,w4,w5,w121] [198,222,327,517,607,672,675] [v378,v379,n977] (by decide +kernel)
def n981 := cc 9 [w65,w0,w1,w2,w3,w4,w123,w5] [245,315,524,636,675] [n352,n914] (by decide +kernel)
def n982 := cc 8 [w413,w1,w2,w3,w4,w121,w13] [90,143,672,687] [] (by decide +kernel)
def n983 := cc 8 [w220,w1,w2,w3,w4,w121,w13] [97,676,684,687] [] (by decide +kernel)
def n984 := cc 8 [w0,w134,w1,w2,w3,w4,w121,w13] [90,143,223,671,676,687] [] (by decide +kernel)
def n985 := cc 8 [w0,w1,w414,w2,w3,w4,w121,w13] [42,179,223,329,662,675,676] [] (by decide +kernel)
def n986 := cc 8 [w47,w0,w1,w2,w3,w4,w121] [146,606,671,672] [n845] (by decide +kernel)
def n987 := cc 8 [w47,w0,w1,w2,w3,w4,w121,w13] [42,90,329,420,676,684] [] (by decide +kernel)
def n988 := cc 8 [w0,w1,w2,w226,w3,w4,w121,w13] [90,223,329,564,662,671,676] [] (by decide +kernel)
def n989 := cc 8 [w0,w1,w2,w3,w415,w121,w13] [90,564,670,672] [] (by decide +kernel)
def n990 := cc 8 [w341,w0,w1,w2,w3,w123,w13] [459,666,669,671] [] (by decide +kernel)
def v380 : Closed T 8 := rotateClosed n874 auto1 auto1ok
def v381 : Closed T 8 := rotateClosed n990 auto1 auto1ok
def v382 : Closed T 8 := rotateClosed n945 auto1 auto1ok
def v383 : Closed T 8 := rotateClosed n862 auto1 auto1ok
def v384 : Closed T 8 := rotateClosed n961 auto1 auto1ok
def n991 := cc 9 [w0,w1,w2,w3,w4,w121,w13] [97,143,389,607,675,676] [n38,v380,v381,n787,n904,n973,v382,n986,n987,n511,n619,n757,n983,n982,n774,n846,n871,v383,n984,n892,n985,n192,n988,n989,n918,n354,n751,v384] (by decide +kernel)
def n992 := cc 7 [w341,w220,w1,w2,w3,w4] [83,90,442,584,662] [] (by decide +kernel)
def n993 := cc 8 [w220,w1,w2,w3,w4,w123,w5] [83,452,601,662,671] [n992] (by decide +kernel)
def n994 := cc 8 [w341,w0,w1,w2,w3,w4,w13] [83,517,581,669] [n992] (by decide +kernel)
def n995 := cc 9 [w0,w1,w2,w3,w4,w123,w5,w13] [97,214,389,459,524,666,671,675] [n994,n993,n754] (by decide +kernel)
def n996 := cc 8 [w0,w1,w2,w229,w3,w123,w5] [179,389,666] [] (by decide +kernel)
def n997 := cc 8 [w0,w1,w2,w3,w416,w4,w121] [118,179,607,664] [] (by decide +kernel)
def n998 := cc 8 [w0,w1,w2,w3,w4,w121,w13] [42,90,143,223,420,517,672] [] (by decide +kernel)
def v385 : Closed T 8 := rotateClosed n997 auto1 auto1ok
def v386 : Closed T 8 := rotateClosed n998 auto1 auto1ok
def n999 := cc 9 [w70,w0,w1,w2,w3,w123,w5] [97,389,483,524,671,675] [n946,n355,n996,v385,v386] (by decide +kernel)
def n1000 := cc 8 [w417,w1,w2,w3,w4,w5,w121] [90,420,564,666] [] (by decide +kernel)
def n1001 := cc 8 [w70,w340,w0,w1,w2,w3,w5] [564,664,670] [] (by decide +kernel)
def n1002 := cc 9 [w70,w0,w1,w2,w3,w4,w5,w121] [97,222,247,420,459,517,564,672,675] [n1001,n754,n998,n1000] (by decide +kernel)
def n1003 := cc 8 [w341,w0,w1,w2,w3,w4,w5] [41,90,161,325,438,666] [] (by decide +kernel)
def n1004 := cc 7 [w337,w0,w1,w2,w3,w4] [636,666,669] [n718] (by decide +kernel)
def v387 : Closed T 7 := rotateClosed n1004 auto1 auto1ok
def n1005 := cc 8 [w0,w1,w2,w3,w415,w5,w125] [90,420,672] [v387] (by decide +kernel)
def v388 : Closed T 8 := rotateClosed n1003 auto1 auto1ok
def n1006 := cc 9 [w0,w1,w2,w3,w415,w4,w5,w121] [97,420,459,564,672] [v388,n1005,n989] (by decide +kernel)
def n1007 := cc 8 [w220,w0,w1,w2,w3,w4,w5] [0,143,233,269,662,671,672] [] (by decide +kernel)
def n1008 := cc 8 [w220,w1,w2,w3,w4,w5,w125] [0,83,90,684,687] [n992] (by decide +kernel)
def n1009 := cc 8 [w0,w357,w1,w2,w3,w4,w5] [143,179,184,267,420,483] [] (by decide +kernel)
def n1010 := cc 7 [w358,w0,w357,w1,w2,w3,w4,w5] [179,218,423] [] (by decide +kernel)
def n1011 := cc 8 [w0,w357,w1,w2,w3,w4,w5,w125] [83,90,143,218,320,420,483,565,671] [n1010,n777,n849] (by decide +kernel)
def n1012 := cc 8 [w0,w1,w391,w2,w3,w4,w5,w125] [83,179,218,320,483,567,675,677] [n906] (by decide +kernel)
def n1013 := cc 8 [w358,w0,w1,w2,w3,w4,w5] [83,90,179,267,269,422,637] [n779,n851,n895] (by decide +kernel)
def n1014 := cc 7 [w0,w418,w1,w2,w3,w4,w5,w125] [83,90,144,146,423,684] [] (by decide +kernel)
def n1015 := cc 7 [w358,w0,w1,w2,w419,w3,w4,w5] [39,179,218,269,571] [] (by decide +kernel)
def n1016 := cc 8 [w358,w0,w1,w2,w3,w4,w5,w125] [83,90,218,320,420,570,671] [n780,n1010,n896,n1015,n1014] (by decide +kernel)
def n1017 := cc 8 [w0,w1,w2,w419,w3,w4,w5,w125] [83,90,218,320,356,564,636,671,677] [n1015] (by decide +kernel)
def n1018 := cc 8 [w341,w0,w1,w2,w3,w4,w125] [0,83,669,671] [n752,n992] (by decide +kernel)
def v389 : Closed T 8 := rotateClosed n1018 auto1 auto1ok
def v390 : Closed T 8 := rotateClosed n930 auto1 auto1ok
def v391 : Closed T 8 := rotateClosed n916 auto1 auto1ok
def n1019 := cc 9 [w0,w1,w2,w3,w4,w5,w125] [83,143,184,269,483,564,675] [n35,n1003,v388,n1018,v389,n788,n907,n930,v390,n1013,n1016,n512,n620,n1007,n1008,n781,n852,n1009,n1011,n897,n1012,n193,n1017,n357,n916,v391] (by decide +kernel)
def n1020 := cc 8 [w0,w357,w1,w2,w3,w4,w123,w5] [83,179,218,483,669,680] [] (by decide +kernel)
def v392 : Closed T 8 := rotateClosed n1005 auto1 auto1ok
def n1021 := cc 9 [w0,w1,w2,w3,w4,w123,w5,w125] [214,315,483,564,666,671,675] [v296,n1018,n993,n722,n783,n854,n1020,n899,v392] (by decide +kernel)
def n1022 := cc 8 [w0,w420,w1,w2,w3,w4,w5] [177,179,184,267,420,496] [] (by decide +kernel)
def n1023 := cc 8 [w0,w1,w2,w368,w3,w4,w5] [90,179,267,269,477,517,582] [n856] (by decide +kernel)
def v393 : Closed T 8 := rotateClosed n1001 auto1 auto1ok
def v394 : Closed T 8 := rotateClosed n1022 auto1 auto1ok
def n1024 := cc 9 [w341,w0,w1,w2,w3,w4,w5] [90,97,161,184,269,389,483,581,666,671,673] [n944,n861,v393,n931,n758,n784,n857,n900,n753,n994,n1018,n917,v394,n1023,n754] (by decide +kernel)
def n1025 := cc 8 [w339,w340,w0,w1,w2,w3,w5] [564,664,670] [v387] (by decide +kernel)
def v395 : Closed T 8 := rotateClosed n1025 auto1 auto1ok
def n1026 := cc 9 [w341,w0,w1,w2,w3,w4,w123,w5] [97,389,459,666,669,671] [v395,n724,n1018,n990] (by decide +kernel)
def n1027 := cc 9 [w339,w0,w1,w2,w3,w4,w5,w121] [222,420,512,564,671,672,675] [n1025,n754,n756,n1000] (by decide +kernel)
def v396 : Closed T 9 := rotateClosed n865 auto1 auto1ok
def v397 : Closed T 9 := rotateClosed n941 auto1 auto1ok
def v398 : Closed T 9 := rotateClosed n976 auto1 auto1ok
def v399 : Closed T 9 := rotateClosed n1027 auto1 auto1ok
def v400 : Closed T 9 := rotateClosed n927 auto1 auto1ok
def v401 : Closed T 9 := rotateClosed n1002 auto1 auto1ok
def v402 : Closed T 9 := rotateClosed n974 auto1 auto1ok
def v403 : Closed T 9 := rotateClosed n759 auto1 auto1ok
def v404 : Closed T 9 := rotateClosed n872 auto1 auto1ok
def v405 : Closed T 9 := rotateClosed n954 auto1 auto1ok
def v406 : Closed T 9 := rotateClosed n980 auto1 auto1ok
def v407 : Closed T 9 := rotateClosed n1006 auto1 auto1ok
def v408 : Closed T 9 := rotateClosed n920 auto1 auto1ok
def v409 : Closed T 9 := rotateClosed n991 auto1 auto1ok
def n1028 := cc 10 [w0,w1,w2,w3,w4,w123,w5] [97,184,269,389,459,524] [v21,v396,v397,v398,v399,n875,n969,v400,n981,v401,n999,n1026,n1024,n789,n908,v402,n932,n948,n947,n513,n621,v403,n726,n785,n858,v404,n864,n863,n901,v405,n937,n194,v406,n975,v407,n923,n939,n755,n964,n995,n1021,n359,n1019,v408,v409] (by decide +kernel)
def n1029 := cc 8 [w0,w1,w422,w3,w4,w9,w5] [127,179,389,517,521] [] (by decide +kernel)
def n1030 := cc 8 [w118,w0,w1,w424,w3,w4,w5] [155,178,521,591] [] (by decide +kernel)
def n1031 := cc 8 [w0,w1,w422,w3,w4,w5,w15] [97,179,472,517] [] (by decide +kernel)
def n1032 := cc 8 [w118,w0,w1,w422,w3,w4,w5] [178,472,521,632] [] (by decide +kernel)
def n1033 := cc 8 [w0,w1,w2,w3,w4,w425,w5] [83,90,127,179,269,517,635] [] (by decide +kernel)
def n1034 := cc 8 [w426,w0,w1,w2,w3,w4,w5] [83,90,155,178,269,562] [] (by decide +kernel)
def n1035 := cc 8 [w65,w0,w1,w2,w424,w3,w4,w5] [159,364,556,646] [] (by decide +kernel)
def n1036 := cc 8 [w0,w1,w2,w422,w3,w4,w5,w13] [90,143,178,517,521,632] [] (by decide +kernel)
def v410 : Closed T 8 := rotateClosed n1030 auto1 auto1ok
def v411 : Closed T 8 := rotateClosed n1034 auto1 auto1ok
def v412 : Closed T 8 := rotateClosed n1035 auto1 auto1ok
def n1037 := cc 9 [w0,w1,w2,w422,w3,w4,w5] [97,178,269,389,517,632] [n1032,v410,v411,n336,v412,n1036,n1033,v131,n1029,n1031] (by decide +kernel)
def n1038 := cc 7 [w1,w2,w351,w3,w4,w427,w5] [98,178,634] [] (by decide +kernel)
def n1039 := cc 8 [w0,w1,w350,w2,w3,w4,w427,w5] [83,98,242,581,636,664] [n1038] (by decide +kernel)
def n1040 := cc 8 [w0,w1,w2,w3,w4,w428,w15] [136,179,184,664] [] (by decide +kernel)
def n1041 := cc 8 [w179,w0,w1,w2,w3,w427,w5] [83,90,101,179,420,438,581] [] (by decide +kernel)
def n1042 := cc 8 [w429,w0,w1,w2,w3,w4,w5] [0,165,179,269,517,521] [] (by decide +kernel)
def n1043 := cc 8 [w0,w1,w2,w3,w4,w428,w13] [83,90,143,179,420,517,564] [] (by decide +kernel)
def n1044 := cc 8 [w70,w0,w1,w2,w3,w427,w5] [161,179,517,581,664] [] (by decide +kernel)
def v413 : Closed T 8 := rotateClosed n1040 auto1 auto1ok
def v414 : Closed T 8 := rotateClosed n1043 auto1 auto1ok
def n1045 := cc 9 [w0,w1,w2,w3,w4,w427,w5] [83,97,184,269,636,664,671] [n1044,n1003,n1041,n1042,n1039,n1033,n754,v413,v414] (by decide +kernel)
def n1046 := cc 9 [w0,w1,w2,w3,w4,w123,w5] [36,97,214,315,389,459,666,671] [n1003,n349,n191,n754,v357,v386] (by decide +kernel)
def n1047 := cc 6 [w421,w430,w128,w1,w3] [178,243,518,584] [] (by decide +kernel)
def n1048 := cc 7 [w421,w128,w1,w298,w3,w9] [103,179,470,584] [n1047] (by decide +kernel)
def n1049 := cc 8 [w421,w128,w1,w298,w2,w3,w4] [65,101,243,366,442,469] [n1048] (by decide +kernel)
def n1050 := cc 8 [w421,w128,w1,w2,w3,w4,w9] [127,243,442,639] [n1048] (by decide +kernel)
def n1051 := cc 7 [w421,w175,w179,w128,w1,w3] [154,243,442,501] [n1047] (by decide +kernel)
def n1052 := cc 8 [w421,w175,w128,w1,w2,w3,w4] [127,152,243,366,500,584] [n1051] (by decide +kernel)
def n1053 := cc 8 [w421,w179,w128,w1,w2,w3,w4] [127,165,243,442,508,584] [n1051] (by decide +kernel)
def n1054 := cc 9 [w421,w128,w1,w2,w3,w4] [97,607] [n1052,n1053,n1049,n1050] (by decide +kernel)
def n1055 := cc 8 [w0,w1,w431,w2,w3,w4,w5] [83,178,365,389,632] [] (by decide +kernel)
def n1056 := cc 8 [w421,w1,w2,w351,w3,w4,w5] [178,365,632] [n1038] (by decide +kernel)
def n1057 := cc 9 [w421,w0,w1,w350,w2,w3,w4,w5] [98,241,581,607,676] [n1056,n1039,n1055] (by decide +kernel)
def n1058 := cc 8 [w432,w0,w1,w2,w3,w4,w5] [83,179,365,389,655] [] (by decide +kernel)
def n1059 := cc 9 [w421,w164,w0,w1,w2,w3,w4,w5] [97,365,607,671] [n1058] (by decide +kernel)
def n1060 := cc 7 [w0,w1,w433,w3,w9,w5] [103,178,179,581] [] (by decide +kernel)
def n1061 := cc 8 [w0,w1,w433,w2,w3,w4,w5] [178,222,438,581] [n1060] (by decide +kernel)
def n1062 := cc 7 [w421,w434,w1,w2,w3,w4] [102,243,518,584] [] (by decide +kernel)
def n1063 := cc 8 [w421,w0,w1,w2,w3,w4,w299] [90,102,241,581] [n1062] (by decide +kernel)
def n1064 := cc 7 [w421,w430,w0,w1,w3,w5] [178,241,512,517,581,664] [n1047] (by decide +kernel)
def n1065 := cc 8 [w421,w0,w1,w298,w3,w9,w5] [103,179,222,470,581] [n1064,n1048,n1060] (by decide +kernel)
def n1066 := cc 9 [w421,w0,w1,w298,w2,w3,w4,w5] [90,101,222,241,459,469,581] [n1049,n1065,n1063,n1061] (by decide +kernel)
def n1067 := cc 8 [w0,w1,w2,w3,w4,w435,w5] [136,518,671] [] (by decide +kernel)
def v415 : Closed T 8 := rotateClosed n1067 auto1 auto1ok
def n1068 := cc 9 [w421,w0,w1,w2,w3,w4,w9,w5] [127,184,331,365,389,581,671,672] [n1050,n1065,v415,n1033,v413,n1029] (by decide +kernel)
def n1069 := cc 8 [w436,w0,w1,w2,w3,w4,w5] [155,178,521,590] [] (by decide +kernel)
def n1070 := cc 8 [w421,w175,w179,w0,w1,w3,w5] [154,222,241,501,581] [n1051,n1064] (by decide +kernel)
def v416 : Closed T 8 := rotateClosed n1069 auto1 auto1ok
def n1071 := cc 9 [w421,w175,w0,w1,w2,w3,w4,w5] [83,127,152,222,241,365,367,581,651,664] [n1070,n1052,v410,v416] (by decide +kernel)
def n1072 := cc 8 [w437,w0,w1,w2,w3,w4,w5] [127,165,581,664] [] (by decide +kernel)
def n1073 := cc 9 [w421,w179,w0,w1,w2,w3,w4,w5] [165,179,581,664] [n1070,n1053,n1041,n1072] (by decide +kernel)
def n1074 := cc 8 [w421,w174,w1,w2,w3,w4,w5] [90,179,502,655] [] (by decide +kernel)
def n1075 := cc 9 [w421,w0,w1,w2,w3,w4,w5,w15] [97,179,184,459,607,664] [n1074,v131,n925,n1031] (by decide +kernel)
def n1076 := cc 8 [w421,w292,w1,w2,w3,w4,w5] [178,472,632] [] (by decide +kernel)
def n1077 := cc 9 [w421,w118,w0,w1,w2,w3,w4,w5] [155,241,607,664] [n1076,n1032,n336] (by decide +kernel)
def n1078 := cc 8 [w0,w1,w2,w438,w3,w4,w5] [179,182,184,438,636] [] (by decide +kernel)
def n1079 := cc 7 [w421,w439,w1,w2,w3,w4] [111,366,662] [] (by decide +kernel)
def n1080 := cc 8 [w421,w0,w1,w2,w3,w4,w61] [90,111,199,365,438,517] [n1079] (by decide +kernel)
def n1081 := cc 9 [w421,w0,w1,w2,w60,w3,w4,w5] [110,179,198,241,365,438,517,607] [n1080,n1078] (by decide +kernel)
def n1082 := cc 9 [w421,w178,w0,w1,w2,w3,w4,w5] [158,244,365,581,607] [v412] (by decide +kernel)
def n1083 := cc 8 [w421,w220,w1,w2,w3,w4,w5] [90,143,659,662,672] [] (by decide +kernel)
def n1084 := cc 9 [w421,w0,w1,w2,w3,w4,w5,w13] [143,231,241,389,607,664,672] [n1083,n1036,n754,v414,n998] (by decide +kernel)
def n1085 := cc 8 [w421,w417,w1,w2,w3,w4,w5] [161,581,666] [] (by decide +kernel)
def n1086 := cc 9 [w421,w70,w0,w1,w2,w3,w4,w5] [97,459,581,671] [n1085,n1044,n1003] (by decide +kernel)
def v417 : Closed T 9 := rotateClosed n1046 auto1 auto1ok
def n1087 := cc 10 [w421,w0,w1,w2,w3,w4,w5] [97,184,269,389,607] [n1077,n1086,n1071,n1082,n1059,n1073,n1054,n1057,n1066,n1081,n1068,n1075,n1084,n1037,n1045,v417] (by decide +kernel)
def n1088 := cc 8 [w0,w1,w2,w3,w4,w441,w5] [83,179,487,639] [] (by decide +kernel)
def n1089 := cc 8 [w442,w0,w1,w2,w3,w4,w5] [134,512,521,589] [] (by decide +kernel)
def n1090 := cc 8 [w0,w1,w2,w127,w3,w5,w13] [389,459,524,662,672] [] (by decide +kernel)
def v418 : Closed T 8 := rotateClosed n1088 auto1 auto1ok
def n1091 := cc 9 [w0,w1,w2,w127,w3,w4,w5] [97,389,459,524,672] [n1089,n514,n344,n1090,v418,n191,n195] (by decide +kernel)
def n1092 := cc 8 [w126,w0,w1,w2,w3,w129,w5] [143,521,601,662,671] [] (by decide +kernel)
def n1093 := cc 8 [w0,w1,w2,w3,w4,w353,w15] [78,90,184,427,671] [] (by decide +kernel)
def n1094 := cc 8 [w179,w0,w1,w2,w3,w129,w5] [452,469,601,672] [] (by decide +kernel)
def n1095 := cc 8 [w443,w0,w1,w2,w3,w4,w5] [83,179,269,508,563] [] (by decide +kernel)
def n1096 := cc 8 [w0,w1,w2,w3,w4,w129,w15] [184,459,607,662,671] [] (by decide +kernel)
def v419 : Closed T 8 := rotateClosed n756 auto1 auto1ok
def v420 : Closed T 8 := rotateClosed n1093 auto1 auto1ok
def n1097 := cc 9 [w0,w1,w2,w3,w4,w129,w5] [83,143,184,459,607,662] [n1094,n1095,n515,n1092,n1007,n196,n1096,n1088,n754,v419,v420] (by decide +kernel)
def n1098 := cc 8 [w126,w128,w0,w1,w2,w3,w13] [143,179,517,521,601,662] [] (by decide +kernel)
def v421 : Closed T 8 := rotateClosed n1092 auto1 auto1ok
def n1099 := cc 9 [w126,w128,w0,w1,w2,w3,w4,w5] [97,254,258,452,505,601,671,672] [n1098,n1092,v421,n1007] (by decide +kernel)
def n1100 := cc 8 [w0,w444,w1,w2,w3,w4,w15] [178,459,521,607] [] (by decide +kernel)
def n1101 := cc 8 [w126,w0,w1,w2,w3,w5,w44] [179,427,445,574] [] (by decide +kernel)
def n1102 := cc 8 [w46,w126,w0,w1,w2,w3,w5] [445,672] [] (by decide +kernel)
def v422 : Closed T 8 := rotateClosed n1100 auto1 auto1ok
def v423 : Closed T 8 := rotateClosed n1096 auto1 auto1ok
def n1103 := cc 9 [w126,w0,w1,w2,w3,w9,w5] [97,184,389,524,672] [n1102,n516,n1101,n197,v422,v423,v357] (by decide +kernel)
def n1104 := cc 8 [w0,w1,w2,w445,w3,w4,w5] [102,222,452,518,601] [] (by decide +kernel)
def n1105 := cc 8 [w126,w0,w1,w2,w3,w304,w5] [83,106,187,254,401,505,550] [] (by decide +kernel)
def n1106 := cc 7 [w301,w126,w0,w1,w3,w4] [254,518,659,671,672] [] (by decide +kernel)
def n1107 := cc 8 [w126,w0,w1,w300,w3,w4,w15] [254,552,671] [n1106] (by decide +kernel)
def v424 : Closed T 8 := rotateClosed n1104 auto1 auto1ok
def n1108 := cc 9 [w126,w0,w1,w300,w2,w3,w4,w5] [254,550,676] [n1107,n1105,v424] (by decide +kernel)
def n1109 := cc 8 [w446,w0,w1,w2,w3,w4,w5] [487,512,521,639,666] [] (by decide +kernel)
def n1110 := cc 8 [w126,w0,w1,w2,w3,w15,w13] [427,574,664,671] [] (by decide +kernel)
def v425 : Closed T 8 := rotateClosed n1109 auto1 auto1ok
def n1111 := cc 9 [w126,w0,w1,w2,w3,w4,w5,w15] [427,459,574,664,671] [n1107,n1101,n1110,v425,v418,n1093] (by decide +kernel)
def n1112 := cc 8 [w447,w0,w1,w2,w3,w4,w5] [254,445,521,589] [] (by decide +kernel)
def n1113 := cc 8 [w126,w0,w1,w2,w3,w177,w5] [445,672] [] (by decide +kernel)
def n1114 := cc 8 [w118,w181,w126,w0,w1,w3,w4] [157,214,254,447,505,593] [n1106] (by decide +kernel)
def n1115 := cc 9 [w118,w126,w0,w1,w2,w3,w4,w5] [254,589,675] [n1114,n1113,n1112] (by decide +kernel)
def n1116 := cc 8 [w448,w0,w1,w2,w3,w4,w5] [505,603,671] [] (by decide +kernel)
def n1117 := cc 8 [w126,w0,w1,w2,w3,w393,w5] [82,505,671] [] (by decide +kernel)
def n1118 := cc 8 [w179,w128,w0,w1,w2,w3,w13] [452,601,662,672] [] (by decide +kernel)
def v426 : Closed T 8 := rotateClosed n1114 auto1 auto1ok
def v427 : Closed T 8 := rotateClosed n1117 auto1 auto1ok
def v428 : Closed T 8 := rotateClosed n1116 auto1 auto1ok
def n1119 := cc 9 [w179,w128,w0,w1,w2,w3,w4,w5] [452,459,601,672] [n1053,v426,n1118,n1094,v427,v428] (by decide +kernel)
def n1120 := cc 8 [w0,w449,w1,w2,w3,w4,w13] [459,535,666,669] [] (by decide +kernel)
def n1121 := cc 8 [w47,w126,w0,w1,w2,w3,w5] [179,455,662] [] (by decide +kernel)
def v429 : Closed T 8 := rotateClosed n1118 auto1 auto1ok
def v430 : Closed T 8 := rotateClosed n1120 auto1 auto1ok
def n1122 := cc 9 [w126,w0,w1,w2,w3,w5,w13] [143,389,459,524,662,664] [v429,n1121,n517,n1098,n199,n1101,n757,n1110,v430,n1090,v386] (by decide +kernel)
def v431 : Closed T 9 := rotateClosed n1119 auto1 auto1ok
def v432 : Closed T 9 := rotateClosed n1097 auto1 auto1ok
def n1123 := cc 10 [w126,w0,w1,w2,w3,w4,w5] [97,184,389,459,524] [n1115,v431,n518,n1099,n1108,n200,n759,n1111,n1103,n1122,n1091,v432,n1046] (by decide +kernel)
def n1124 := cc 8 [w0,w1,w273,w2,w3,w450,w4,w5] [164,208,251,294,541,623] [] (by decide +kernel)
def n1125 := cc 6 [w0,w1,w2,w3,w355,w354,w13] [107,119,128] [] (by decide +kernel)
def n1126 := cc 7 [w0,w1,w2,w3,w4,w355,w5,w354] [83,90,405,472] [n1125] (by decide +kernel)
def n1127 := cc 7 [w0,w1,w273,w2,w3,w4,w354,w13] [178,260,410] [n1125,n760] (by decide +kernel)
def n1128 := cc 7 [w0,w1,w273,w2,w3,w4,w5,w451] [13,146,179,233,294] [] (by decide +kernel)
def n1129 := cc 7 [w356,w0,w1,w273,w2,w3,w4,w5] [90,257,477] [n761] (by decide +kernel)
def v433 : Closed T 7 := rotateClosed n1127 auto1 auto1ok
def v434 : Closed T 7 := rotateClosed n762 auto1 auto1ok
def n1130 := cc 8 [w0,w1,w273,w2,w3,w4,w355,w5] [178,303,405,477,512,541] [n1129,n1128,v433,n1126,v434] (by decide +kernel)
def n1131 := cc 8 [w452,w0,w1,w2,w3,w4,w5] [83,90,155,241,313,389,623] [] (by decide +kernel)
def n1132 := cc 7 [w453,w0,w1,w273,w2,w3,w4,w5] [211] [] (by decide +kernel)
def n1133 := cc 8 [w0,w1,w273,w2,w3,w4,w12,w5] [138,178,225,294,295,405,623,681] [n1132] (by decide +kernel)
def n1134 := cc 7 [w1,w273,w2,w3,w4,w5,w13,w125] [231,407,440,497,662] [] (by decide +kernel)
def n1135 := cc 7 [w454,w0,w1,w273,w2,w3,w4,w5] [218] [] (by decide +kernel)
def n1136 := cc 8 [w0,w1,w273,w2,w3,w4,w5,w13] [83,90,143,178,231,294,351,405,472,541,623,662] [n1135,n1128,n1127,v433,n1134,n766,n763,v300] (by decide +kernel)
def v435 : Closed T 8 := rotateClosed n1131 auto1 auto1ok
def v436 : Closed T 8 := rotateClosed n1130 auto1 auto1ok
def v437 : Closed T 8 := rotateClosed n1133 auto1 auto1ok
def v438 : Closed T 8 := rotateClosed n771 auto1 auto1ok
def v439 : Closed T 8 := rotateClosed n769 auto1 auto1ok
def n1137 := cc 9 [w0,w1,w273,w2,w3,w4,w5] [0,97,178,184,294,405,472] [n1131,v435,n1124,n1130,v436,n1133,v437,n1136,n771,v438,n584,n769,v439] (by decide +kernel)
def n1138 := cc 8 [w456,w0,w1,w2,w3,w4,w5] [254,512,676] [] (by decide +kernel)
def n1139 := cc 8 [w0,w1,w2,w3,w4,w359,w18] [184,345,346,675] [] (by decide +kernel)
def n1140 := cc 8 [w0,w1,w2,w3,w4,w359,w13] [231,389,622,675] [] (by decide +kernel)
def n1141 := cc 8 [w0,w1,w2,w3,w4,w5,w457] [83,231,269,542,675] [] (by decide +kernel)
def n1142 := cc 8 [w458,w0,w1,w2,w3,w4,w5] [90,247,343,445,624,666] [] (by decide +kernel)
def v440 : Closed T 8 := rotateClosed n1139 auto1 auto1ok
def v441 : Closed T 8 := rotateClosed n1140 auto1 auto1ok
def n1143 := cc 9 [w0,w1,w2,w3,w4,w455,w5] [97,184,331,389,459,540,676] [n1142,n1138,n771,n1141,v302,v440,v441] (by decide +kernel)
def n1144 := cc 9 [w0,w272,w459,w3,w4,w5] [97,184,269,389] [] (by decide +kernel)
def n1145 := cc 8 [w203,w0,w272,w1,w2,w3,w4,w5] [138,228,622,676,681] [] (by decide +kernel)
def n1146 := cc 8 [w460,w0,w1,w2,w3,w4,w5] [225,267,622,681] [] (by decide +kernel)
def n1147 := cc 9 [w0,w272,w1,w2,w3,w4,w12,w5] [138,225,269,270,389,622] [n1146,n1145,n1133,v440] (by decide +kernel)
def n1148 := cc 7 [w362,w0,w1,w2,w3,w4,w5,w13] [144,146,422,435,493] [] (by decide +kernel)
def n1149 := cc 7 [w358,w0,w272,w1,w3,w4,w5,w13] [83,90,422] [] (by decide +kernel)
def n1150 := cc 8 [w0,w272,w1,w2,w3,w4,w5,w13,w125] [83,90,143,231,420,438,496,680,684] [n1149,n1148,n1134] (by decide +kernel)
def n1151 := cc 8 [w220,w0,w272,w1,w2,w3,w4,w5] [10,56,143,233,356,675,676,684] [] (by decide +kernel)
def n1152 := cc 7 [w0,w461,w1,w2,w3,w4,w5] [0,132,146,269,662] [] (by decide +kernel)
def v442 : Closed T 7 := rotateClosed n773 auto1 auto1ok
def n1153 := cc 8 [w361,w0,w1,w2,w3,w4,w5] [97,231,357,544,625,662] [n773,v442,n1152] (by decide +kernel)
def n1154 := cc 9 [w0,w272,w1,w2,w3,w4,w5,w13] [83,143,231,351,389,459,540,622,684] [n1153,n1151,n1150,n781,n774,v301,n1136,n1141,n1140,v441] (by decide +kernel)
def v443 : Closed T 9 := rotateClosed n785 auto1 auto1ok
def v444 : Closed T 9 := rotateClosed n1147 auto1 auto1ok
def v445 : Closed T 9 := rotateClosed n1143 auto1 auto1ok
def n1155 := cc 10 [w0,w272,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n587,n785,v443,n1147,v444,n1154,n1144,n1137,n1143,v445] (by decide +kernel)
def n1156 := cc 9 [w0,w1,w2,w462,w4,w5] [97,184,269,389] [] (by decide +kernel)
def n1157 := cc 9 [w463,w0,w1,w2,w4,w5] [0,97,184,389] [] (by decide +kernel)
def n1158 := cc 10 [w0,w1,w2,w459,w3,w4,w5] [97,184,269,389,459] [n1157,n1144,n1156] (by decide +kernel)
def n1159 := cc 8 [w0,w464,w1,w2,w3,w4,w5] [0,269,502,671] [] (by decide +kernel)
def n1160 := cc 8 [w40,w0,w465,w2,w3,w4,w5] [90,179,184,267,459] [] (by decide +kernel)
def n1161 := cc 8 [w0,w1,w2,w3,w4,w466,w5] [83,500,671] [] (by decide +kernel)
def n1162 := cc 8 [w467,w0,w1,w2,w3,w4,w5] [0,179,269,427,487] [] (by decide +kernel)
def n1163 := cc 8 [w40,w0,w1,w2,w3,w4,w13] [90,427,648,671] [] (by decide +kernel)
def n1164 := cc 9 [w40,w0,w1,w2,w3,w4,w5] [97,184,345,389,459,648,671] [n1162,n29,n40,n1160,n1163,n1159,n1161] (by decide +kernel)
def n1165 := cc 8 [w468,w0,w1,w2,w3,w4,w5] [179,225,648] [] (by decide +kernel)
def n1166 := cc 8 [w39,w203,w0,w1,w2,w3,w4,w5] [228,267,450,648] [] (by decide +kernel)
def n1167 := cc 9 [w39,w0,w1,w2,w3,w4,w12,w5] [97,225,267,269,389,648] [n1165,n1166] (by decide +kernel)
def n1168 := cc 8 [w469,w0,w1,w2,w3,w4,w5] [0,179,269,455,508] [] (by decide +kernel)
def n1169 := cc 8 [w39,w0,w1,w2,w3,w4,w5,w13,w125] [83,90,231,420,438,496,517,684] [] (by decide +kernel)
def n1170 := cc 8 [w39,w220,w0,w1,w2,w3,w4,w5] [66,233,269,671,684] [] (by decide +kernel)
def v446 : Closed T 8 := rotateClosed n1163 auto1 auto1ok
def n1171 := cc 9 [w39,w0,w1,w2,w3,w4,w5,w13] [83,143,231,351,389,459,585,648,684] [n1162,n1163,v446,n30,n1168,n41,n1170,n1169,n788,n787,v303] (by decide +kernel)
def v447 : Closed T 9 := rotateClosed n1164 auto1 auto1ok
def v448 : Closed T 9 := rotateClosed n789 auto1 auto1ok
def v449 : Closed T 9 := rotateClosed n1167 auto1 auto1ok
def n1172 := cc 10 [w39,w0,w1,w2,w3,w4,w5] [0,97,184,269,389,459] [n1164,v447,n31,n42,n590,n789,v448,n1167,v449,n1171] (by decide +kernel)
def n1173 := cc 10 [w470,w0,w1,w2,w3,w4,w5] [97,184,269,389,459] [] (by decide +kernel)
def n1174 := cc 6 [w0,w1,w145,w3,w4,w137,w15] [105,114,124] [] (by decide +kernel)
def v450 : Closed T 6 := rotateClosed n1174 auto1 auto1ok
def n1175 := cc 7 [w0,w1,w2,w145,w3,w4,w138,w5] [83,179,208,415] [v450] (by decide +kernel)
def n1176 := cc 7 [w0,w1,w136,w145,w3,w4,w9,w5] [182,380,409,415] [v450,v305] (by decide +kernel)
def n1177 := cc 6 [w472,w0,w1,w136,w2,w3,w4] [] [] (by decide +kernel)
def n1178 := cc 7 [w0,w1,w136,w2,w3,w4,w471,w5] [19,133,342,480] [n1177] (by decide +kernel)
def n1179 := cc 7 [w365,w0,w1,w136,w2,w3,w4,w5] [64,90,382,476] [n791] (by decide +kernel)
def v451 : Closed T 7 := rotateClosed n1179 auto1 auto1ok
def v452 : Closed T 7 := rotateClosed n1178 auto1 auto1ok
def v453 : Closed T 7 := rotateClosed n1176 auto1 auto1ok
def v454 : Closed T 7 := rotateClosed n1175 auto1 auto1ok
def v455 : Closed T 7 := rotateClosed n792 auto1 auto1ok
def n1180 := cc 8 [w0,w1,w136,w2,w145,w3,w4,w5] [182,208,409,415,476,480,668,677] [n1179,v451,n1178,v452,n1176,v453,n1175,v454,n792,v455] (by decide +kernel)
def n1181 := cc 8 [w473,w0,w1,w2,w3,w4,w5] [90,179,360,459,517] [] (by decide +kernel)
def n1182 := cc 6 [w0,w1,w2,w3,w138,w137,w13] [116,120,139] [] (by decide +kernel)
def n1183 := cc 7 [w0,w1,w2,w3,w4,w138,w5,w137] [83,90,415,480] [n1182] (by decide +kernel)
def n1184 := cc 7 [w0,w1,w136,w2,w3,w4,w137,w15] [182,212,386] [n1174,n216] (by decide +kernel)
def n1185 := cc 7 [w139,w0,w1,w136,w2,w3,w4,w5] [179,211,314] [n217] (by decide +kernel)
def n1186 := cc 7 [w0,w1,w136,w2,w3,w4,w137,w13] [182,387,418] [n1182,n793] (by decide +kernel)
def n1187 := cc 6 [w475,w0,w1,w136,w3,w4,w5] [] [] (by decide +kernel)
def n1188 := cc 7 [w0,w1,w136,w2,w3,w4,w5,w474] [19,147,208,356] [n1187] (by decide +kernel)
def n1189 := cc 7 [w366,w0,w1,w136,w2,w3,w4,w5] [90,384,482] [n794] (by decide +kernel)
def v456 : Closed T 7 := rotateClosed n1184 auto1 auto1ok
def v457 : Closed T 7 := rotateClosed n1186 auto1 auto1ok
def v458 : Closed T 7 := rotateClosed n795 auto1 auto1ok
def n1190 := cc 8 [w0,w1,w136,w2,w3,w4,w138,w5] [182,211,415,482,680] [n1189,n1185,n1178,n1188,v456,v457,n1175,n1183,n218,v458] (by decide +kernel)
def n1191 := cc 8 [w476,w0,w1,w2,w3,w4,w5] [159,179,184,365,664] [] (by decide +kernel)
def n1192 := cc 7 [w1,w136,w2,w3,w4,w9,w119,w5] [209,239,331,433,512,680] [] (by decide +kernel)
def n1193 := cc 7 [w477,w0,w1,w136,w2,w3,w4,w5] [303] [] (by decide +kernel)
def n1194 := cc 7 [w0,w1,w136,w2,w3,w4,w15,w13] [86,180,208,415,518,662] [n796,n224,n805,n219] (by decide +kernel)
def n1195 := cc 6 [w478,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n1196 := cc 7 [w0,w1,w136,w2,w3,w4,w5,w44] [83,90,179,182,231,427,487] [n1195,n225,n798,v310,n220] (by decide +kernel)
def n1197 := cc 6 [w479,w1,w136,w2,w3,w4,w5] [90] [] (by decide +kernel)
def n1198 := cc 7 [w46,w0,w1,w136,w2,w3,w4,w5] [83,90,97,247,445,521] [n799,n221,n1197] (by decide +kernel)
def v459 : Closed T 7 := rotateClosed n1194 auto1 auto1ok
def v460 : Closed T 7 := rotateClosed n806 auto1 auto1ok
def n1199 := cc 8 [w0,w1,w136,w2,w3,w4,w9,w5] [83,127,179,182,208,331,415,480,487,512,664] [n1198,n1193,n1178,n1196,v456,v459,n1176,v460,n1192,n227,v315,n222] (by decide +kernel)
def n1200 := cc 7 [w1,w136,w2,w3,w4,w5,w13,w125] [351,417,441,498,662,680] [] (by decide +kernel)
def n1201 := cc 7 [w480,w0,w1,w136,w2,w3,w4,w5] [320] [] (by decide +kernel)
def n1202 := cc 6 [w481,w1,w136,w2,w3,w4,w5] [179] [] (by decide +kernel)
def n1203 := cc 6 [w0,w1,w482,w2,w3,w4,w5] [83] [] (by decide +kernel)
def v461 : Closed T 6 := rotateClosed n807 auto1 auto1ok
def n1204 := cc 7 [w47,w0,w1,w136,w2,w3,w4,w5] [19,83,90,179,182,231,455,508] [n807,v461,n1203,n1202] (by decide +kernel)
def n1205 := cc 8 [w0,w1,w136,w2,w3,w4,w5,w13] [83,90,143,182,208,231,351,415,480,517,662] [n1204,n1201,n1188,n1196,n1186,v457,n1194,v459,n232,n1200,n811,n808,v316] (by decide +kernel)
def v462 : Closed T 8 := rotateClosed n1191 auto1 auto1ok
def v463 : Closed T 8 := rotateClosed n1190 auto1 auto1ok
def v464 : Closed T 8 := rotateClosed n1199 auto1 auto1ok
def v465 : Closed T 8 := rotateClosed n818 auto1 auto1ok
def v466 : Closed T 8 := rotateClosed n815 auto1 auto1ok
def n1206 := cc 9 [w0,w1,w136,w2,w3,w4,w5] [97,182,208,269,415,480] [n1191,v462,n1181,n1180,n1190,v463,n1199,v464,n1205,n235,n818,v465,n233,n815,v466] (by decide +kernel)
def n1207 := cc 8 [w483,w0,w1,w2,w3,w4,w5] [90,251,377,459,671] [] (by decide +kernel)
def n1208 := cc 7 [w0,w168,w42,w3,w4,w5] [179,267,338,543] [] (by decide +kernel)
def n1209 := cc 8 [w0,w1,w42,w3,w4,w9,w5] [179,331,425,521] [n1208] (by decide +kernel)
def n1210 := cc 8 [w0,w1,w2,w3,w4,w484,w5] [83,90,179,333,425,459] [] (by decide +kernel)
def n1211 := cc 8 [w485,w0,w1,w2,w3,w4,w5] [90,369,672] [] (by decide +kernel)
def n1212 := cc 8 [w0,w1,w2,w42,w3,w4,w5,w13] [83,231,351,521,662,671] [] (by decide +kernel)
def v467 : Closed T 8 := rotateClosed n1211 auto1 auto1ok
def v468 : Closed T 8 := rotateClosed n1210 auto1 auto1ok
def v469 : Closed T 8 := rotateClosed n1209 auto1 auto1ok
def n1213 := cc 9 [w0,w1,w2,w42,w3,w4,w5] [97,184,269,389,486,671,672] [n1211,v467,n43,n1207,n1212,n591,n235,n1210,v468,n234,n1209,v469] (by decide +kernel)
def n1214 := cc 8 [w486,w0,w1,w2,w3,w4,w5] [179,184,383,450,676] [] (by decide +kernel)
def n1215 := cc 8 [w0,w1,w2,w3,w4,w369,w15] [230,269,347,675] [] (by decide +kernel)
def n1216 := cc 8 [w487,w0,w1,w2,w3,w4,w5] [98,179,454,521] [] (by decide +kernel)
def n1217 := cc 7 [w0,w1,w2,w3,w43,w15,w13] [226,348,518,676] [] (by decide +kernel)
def n1218 := cc 8 [w0,w1,w2,w3,w4,w43,w5,w15] [90,225,345,427,518,676] [n1217] (by decide +kernel)
def n1219 := cc 7 [w47,w0,w1,w2,w3,w4,w369] [357,675] [] (by decide +kernel)
def v470 : Closed T 7 := rotateClosed n1217 auto1 auto1ok
def n1220 := cc 8 [w0,w1,w2,w3,w4,w369,w13] [351,354,389,517,675] [n1219,v470] (by decide +kernel)
def n1221 := cc 8 [w0,w1,w2,w3,w4,w5,w488] [0,83,179,184,351,490,675] [] (by decide +kernel)
def n1222 := cc 8 [w489,w0,w1,w2,w3,w4,w5] [374,666,675] [] (by decide +kernel)
def v471 : Closed T 8 := rotateClosed n1215 auto1 auto1ok
def v472 : Closed T 8 := rotateClosed n1220 auto1 auto1ok
def n1223 := cc 9 [w0,w1,w2,w3,w4,w43,w5] [97,225,269,459,524,676,680] [n1222,n1216,n44,n1214,n243,n1218,n818,n1210,n1221,v334,v471,v472] (by decide +kernel)
def n1224 := cc 8 [w490,w0,w2,w4,w5] [97,184,269,389] [] (by decide +kernel)
def n1225 := cc 9 [w0,w41,w2,w152,w4,w5] [97,184,269,389] [n1224] (by decide +kernel)
def n1226 := cc 7 [w150,w0,w1,w2,w3,w4,w9,w5] [44,48,127,219,236,434] [] (by decide +kernel)
def n1227 := cc 8 [w0,w41,w1,w2,w3,w4,w9,w119,w5] [83,127,179,214,238,331,431,678,680,685] [n1226,n1192] (by decide +kernel)
def n1228 := cc 6 [w492,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n1229 := cc 7 [w0,w41,w1,w2,w3,w4,w491,w5] [0,83,179,259,269,429,503,664] [n1228] (by decide +kernel)
def n1230 := cc 6 [w148,w167,w0,w1,w2,w3,w5] [] [] (by decide +kernel)
def n1231 := cc 7 [w167,w0,w41,w1,w2,w3,w5,w13] [180,268,488,512,675] [n1230] (by decide +kernel)
def v473 : Closed T 7 := rotateClosed n1229 auto1 auto1ok
def n1232 := cc 8 [w167,w0,w41,w1,w2,w3,w4,w5] [127,179,267,342,459,675,676,678] [n1231,v473] (by decide +kernel)
def n1233 := cc 6 [w0,w493,w1,w2,w3,w5,w13] [459] [] (by decide +kernel)
def n1234 := cc 7 [w0,w493,w1,w2,w3,w4,w5] [0,90,133,459,512] [n1233] (by decide +kernel)
def n1235 := cc 6 [w147,w220,w0,w1,w2,w3,w5] [] [] (by decide +kernel)
def n1236 := cc 7 [w147,w0,w1,w2,w3,w5,w13] [49,471,489,512] [n1235,n820,n838,n244,n1233] (by decide +kernel)
def n1237 := cc 8 [w147,w0,w1,w2,w3,w4,w5] [90,133,331,489,512] [n839,n822,n1236,n245,n1234] (by decide +kernel)
def n1238 := cc 7 [w0,w41,w399,w2,w3,w4,w5] [179,303,304,682] [] (by decide +kernel)
def n1239 := cc 8 [w0,w41,w168,w2,w3,w4,w5] [184,331,334,540,682] [n1238,n1208] (by decide +kernel)
def v474 : Closed T 6 := rotateClosed n1235 auto1 auto1ok
def n1240 := cc 7 [w220,w0,w41,w1,w2,w3,w4,w15] [180,233,662,675,676] [v474] (by decide +kernel)
def n1241 := cc 6 [w0,w494,w1,w2,w3,w4,w15] [184] [] (by decide +kernel)
def v475 : Closed T 6 := rotateClosed n1230 auto1 auto1ok
def n1242 := cc 7 [w148,w0,w1,w2,w3,w4,w15] [201,234,662] [v475,n256,n840,n246,n1241] (by decide +kernel)
def v476 : Closed T 7 := rotateClosed n1236 auto1 auto1ok
def v477 : Closed T 7 := rotateClosed n1231 auto1 auto1ok
def n1243 := cc 8 [w0,w41,w1,w2,w3,w4,w15,w13] [90,137,231,348,517,574,680,686,687] [v476,n1242,n45,v477,n1240,n824,n257,n841,n247,n1194,n1217] (by decide +kernel)
def n1244 := cc 7 [w45,w0,w41,w1,w2,w3,w4,w5] [83,90,179,233,267,269,428,488] [n1195,n63,n46,n627] (by decide +kernel)
def n1245 := cc 6 [w0,w495,w1,w2,w3,w4,w5] [0,97] [] (by decide +kernel)
def v478 : Closed T 6 := rotateClosed n826 auto1 auto1ok
def n1246 := cc 7 [w149,w0,w1,w2,w3,w4,w5] [0,97,234,430,489] [n1195,n826,v478,n248,n1245] (by decide +kernel)
def n1247 := cc 7 [w149,w0,w1,w2,w3,w4,w5,w44] [83,90,179,232,262,264] [] (by decide +kernel)
def n1248 := cc 7 [w0,w41,w496,w2,w3,w4,w5,w44] [83,179,339,340,575] [] (by decide +kernel)
def n1249 := cc 8 [w0,w41,w1,w2,w3,w4,w5,w44] [83,90,97,179,231,267,339,487,574,678,679,684] [n1246,n1247,n47,n1244,n1248,n261,n827,v325,n249,n1196] (by decide +kernel)
def n1250 := cc 7 [w149,w0,w1,w2,w3,w4,w9,w5] [44,48,229,234,263,426] [] (by decide +kernel)
def n1251 := cc 8 [w0,w41,w1,w2,w3,w4,w9,w5,w44] [83,179,266,339,455,487,574,664,678,680,685] [n1250] (by decide +kernel)
def n1252 := cc 7 [w0,w479,w41,w1,w2,w3,w4,w5] [248,521,666,675] [n1197] (by decide +kernel)
def n1253 := cc 8 [w46,w0,w41,w1,w2,w3,w4,w5] [134,343,487,521,589,666,678] [n48,n828,n250,n1198,n1252] (by decide +kernel)
def v479 : Closed T 8 := rotateClosed n842 auto1 auto1ok
def v480 : Closed T 8 := rotateClosed n1243 auto1 auto1ok
def v481 : Closed T 8 := rotateClosed n1218 auto1 auto1ok
def n1254 := cc 9 [w0,w41,w1,w2,w3,w4,w9,w5] [83,127,184,331,487,524,685] [n1253,n1237,n49,n1232,n1239,v479,n1227,n1251,n263,n1249,v332,v480,n251,n1199,v481,n1210,v471,n1209] (by decide +kernel)
def n1255 := cc 7 [w371,w0,w1,w2,w3,w4,w5,w13] [54,57,143,424,437,495] [] (by decide +kernel)
def n1256 := cc 8 [w0,w41,w1,w2,w3,w4,w5,w13,w125] [83,90,143,351,420,438,496,680,684,687] [n1255,n1200] (by decide +kernel)
def n1257 := cc 6 [w498,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n1258 := cc 7 [w0,w41,w1,w2,w497,w3,w4,w5] [179,233,267,269,675,676] [n1257] (by decide +kernel)
def v482 : Closed T 7 := rotateClosed n1240 auto1 auto1ok
def n1259 := cc 8 [w220,w0,w41,w1,w2,w3,w4,w5] [143,233,267,356,671,675,676,684] [n1240,v482,n1258] (by decide +kernel)
def v483 : Closed T 6 := rotateClosed n1241 auto1 auto1ok
def n1260 := cc 7 [w0,w494,w1,w2,w3,w4,w5] [0,147,179,184,662] [n1241,v483] (by decide +kernel)
def v484 : Closed T 7 := rotateClosed n843 auto1 auto1ok
def v485 : Closed T 7 := rotateClosed n1242 auto1 auto1ok
def n1261 := cc 8 [w148,w0,w1,w2,w3,w4,w5] [147,179,234,351,662] [n269,n843,v484,n1242,v485,n1260] (by decide +kernel)
def n1262 := cc 7 [w0,w41,w135,w2,w3,w4,w5] [143,267,320,321,322] [n270] (by decide +kernel)
def n1263 := cc 8 [w0,w41,w134,w2,w3,w4,w5] [143,231,267,351,352,354,459,545] [n271,n1262] (by decide +kernel)
def n1264 := cc 7 [w149,w0,w1,w2,w3,w4,w5,w13] [54,57,231,430,444,499] [] (by decide +kernel)
def n1265 := cc 8 [w0,w41,w1,w2,w3,w4,w5,w13,w44] [83,90,231,351,427,445,500,517,680,684,687] [n1264] (by decide +kernel)
def n1266 := cc 7 [w0,w481,w41,w1,w2,w3,w4,w5] [0,179,269,456,675,676] [n1203,n1202] (by decide +kernel)
def n1267 := cc 6 [w499,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def v486 : Closed T 6 := rotateClosed n844 auto1 auto1ok
def n1268 := cc 7 [w0,w1,w48,w2,w3,w4,w5] [97,227,357,509,605] [n50,n1267,n844,v486,n1203] (by decide +kernel)
def v487 : Closed T 7 := rotateClosed n845 auto1 auto1ok
def v488 : Closed T 7 := rotateClosed n1219 auto1 auto1ok
def n1269 := cc 8 [w47,w0,w41,w1,w2,w3,w4,w5] [146,231,357,603,684] [n51,n845,v487,n1204,n1219,v488,n1266,n1268] (by decide +kernel)
def n1270 := cc 9 [w0,w41,w1,w2,w3,w4,w5,w13] [83,143,231,351,459,524,687] [n1269,n1261,n52,n1259,n1263,n272,n1256,n1265,n852,n1249,n846,v333,n1243,v480,n1205,n1212,n1221,n1220,v472] (by decide +kernel)
def v489 : Closed T 9 := rotateClosed n858 auto1 auto1ok
def v490 : Closed T 9 := rotateClosed n1254 auto1 auto1ok
def v491 : Closed T 9 := rotateClosed n1223 auto1 auto1ok
def n1271 := cc 10 [w0,w41,w1,w2,w3,w4,w5] [97,184,269,389,459] [n53,n273,n858,v489,n1254,v490,n1270,n592,n1225,n1206,n1213,n1223,v491] (by decide +kernel)
def n1272 := cc 10 [w0,w1,w2,w3,w152,w4,w5] [0,97,184,389,459] [n1225] (by decide +kernel)
def n1273 := cc 9 [w154,w500,w0,w2,w4,w5] [0,97,184,389] [n1224] (by decide +kernel)
def n1274 := cc 10 [w154,w0,w1,w2,w3,w4,w5] [97,184,269,524,607] [n1273,n274] (by decide +kernel)
def n1275 := cc 10 [w500,w0,w1,w2,w3,w4,w5] [97,184,269,389,459] [n1273] (by decide +kernel)
def n1276 := cc 8 [w501,w0,w1,w2,w3,w4,w5] [165,521,577] [] (by decide +kernel)
def n1277 := cc 8 [w502,w0,w1,w2,w3,w4,w5] [90,161,179,184,438,581] [] (by decide +kernel)
def n1278 := cc 8 [w0,w1,w156,w2,w3,w5,w13] [143,217,483,521,524,662,671] [n275,n866] (by decide +kernel)
def n1279 := cc 9 [w0,w1,w156,w2,w3,w4,w5] [97,214,483,524,671,675] [n1277,n1276,n1278,n278,v338,n276,n867] (by decide +kernel)
def n1280 := cc 8 [w503,w0,w1,w2,w3,w4,w5] [448,597,672] [] (by decide +kernel)
def n1281 := cc 7 [w0,w1,w157,w3,w15,w13] [180,231,574] [] (by decide +kernel)
def n1282 := cc 8 [w0,w1,w157,w3,w4,w5,w15] [179,487,574] [n1281] (by decide +kernel)
def n1283 := cc 8 [w0,w1,w2,w3,w4,w505,w5] [0,179,269,427,487] [] (by decide +kernel)
def n1284 := cc 8 [w506,w0,w1,w2,w3,w4,w5] [90,247,445,521,589] [] (by decide +kernel)
def n1285 := cc 8 [w0,w1,w2,w157,w3,w5,w13] [231,459,524,672] [n1281] (by decide +kernel)
def v492 : Closed T 8 := rotateClosed n1283 auto1 auto1ok
def n1286 := cc 9 [w0,w1,w2,w157,w3,w4,w5] [97,184,459,524,672] [n1284,n1280,n1285,n278,v492,n277,n1282] (by decide +kernel)
def n1287 := cc 8 [w507,w0,w1,w2,w3,w4,w5] [0,143,233,269,662,672] [] (by decide +kernel)
def n1288 := cc 8 [w0,w1,w2,w3,w4,w379,w15] [231,574,671] [] (by decide +kernel)
def n1289 := cc 8 [w508,w0,w1,w2,w3,w4,w5] [0,179,269,455,508] [] (by decide +kernel)
def v493 : Closed T 8 := rotateClosed n868 auto1 auto1ok
def v494 : Closed T 8 := rotateClosed n1288 auto1 auto1ok
def n1290 := cc 9 [w0,w1,w2,w3,w4,w161,w5] [83,143,231,389,607,662] [n1289,n1287,n280,n869,n1283,v493,v494] (by decide +kernel)
def n1291 := cc 8 [w509,w0,w1,w2,w3,w4,w5] [134,343,487,512,521,549,666] [] (by decide +kernel)
def n1292 := cc 8 [w0,w155,w1,w2,w3,w15,w13] [231,459,574,671] [n1281] (by decide +kernel)
def v495 : Closed T 8 := rotateClosed n1291 auto1 auto1ok
def n1293 := cc 9 [w0,w155,w1,w2,w3,w4,w5,w15] [184,459,574,671] [v495,n1292,v492,n1288,n1282] (by decide +kernel)
def n1294 := cc 9 [w0,w155,w1,w2,w3,w5,w13] [143,231,389,459,524,662,664] [n282,n871,n1292,n1278,n1285] (by decide +kernel)
def v496 : Closed T 9 := rotateClosed n1290 auto1 auto1ok
def n1295 := cc 10 [w0,w155,w1,w2,w3,w4,w5] [97,184,389,459,524] [n283,n872,n1293,n1294,n1279,n1286,v496] (by decide +kernel)
def n1296 := cc 10 [w0,w1,w2,w3,w4,w510,w5] [97,184,269,389,459] [] (by decide +kernel)
def n1297 := cc 8 [w0,w511,w1,w2,w3,w4,w5] [143,179,233,356,588,675] [] (by decide +kernel)
def n1298 := cc 8 [w50,w0,w134,w2,w3,w4,w5] [267,389,459,675] [] (by decide +kernel)
def n1299 := cc 8 [w0,w1,w2,w512,w3,w4,w5] [0,179,269,455,508] [] (by decide +kernel)
def n1300 := cc 9 [w50,w0,w1,w2,w3,w4,w5] [97,231,351,389,459,587,675,684] [n1162,n35,n54,n1298,n284,n1297,n1299] (by decide +kernel)
def n1301 := cc 8 [w513,w0,w1,w2,w3,w4,w5] [0,247,269,675] [] (by decide +kernel)
def n1302 := cc 7 [w49,w167,w0,w1,w2,w3,w13] [69,87,256,488,675] [] (by decide +kernel)
def n1303 := cc 8 [w49,w167,w0,w1,w2,w3,w4,w5] [47,68,127,179,342,448,488,512,521] [n1302] (by decide +kernel)
def n1304 := cc 7 [w49,w0,w134,w2,w3,w9,w13] [70,662,675] [] (by decide +kernel)
def n1305 := cc 8 [w49,w0,w1,w2,w3,w9,w13] [231,337,487,512,587,672,675,684] [n36,n55,n1302,n1304,n287,n285] (by decide +kernel)
def n1306 := cc 9 [w49,w0,w1,w2,w3,w4,w9,w5] [97,184,331,389,487,512,587,672] [n1162,n37,n1301,n56,n1303,n288,n873,n1305,n286] (by decide +kernel)
def n1307 := cc 8 [w49,w0,w134,w2,w3,w4,w13] [231,268,351,662,675] [n1304] (by decide +kernel)
def n1308 := cc 9 [w49,w0,w1,w2,w3,w4,w13] [231,351,389,459,607,675,684] [n1163,n38,n57,n1307,n291,n874,n1305] (by decide +kernel)
def n1309 := cc 10 [w49,w0,w1,w2,w3,w4,w5] [97,184,269,389,459,607] [n1300,n1164,n39,n58,n292,n875,n1306,n1308] (by decide +kernel)
def n1310 := cc 9 [w0,w1,w2,w3,w4,w515] [97,184,269,389] [] (by decide +kernel)
def n1311 := cc 9 [w0,w517,w1,w2,w3,w5] [97,184,269,389] [] (by decide +kernel)
def n1312 := cc 9 [w49,w516,w0,w2,w3,w4] [] [] (by decide +kernel)
def v497 : Closed T 9 := rotateClosed n1312 auto1 auto1ok
def v498 : Closed T 9 := rotateClosed n1311 auto1 auto1ok
def n1313 := cc 10 [w514,w0,w1,w2,w3,w4,w5] [97,184,269,389,459] [v497,v498,n1310] (by decide +kernel)
def n1314 := cc 6 [w0,w1,w2,w3,w383,w382,w13] [194,205,215] [] (by decide +kernel)
def n1315 := cc 7 [w0,w1,w2,w3,w4,w383,w5,w382] [83,90,400,468] [n1314] (by decide +kernel)
def n1316 := cc 7 [w0,w1,w2,w351,w3,w4,w382,w13] [178,260,561] [n1314,n876] (by decide +kernel)
def n1317 := cc 6 [w0,w519,w2,w351,w3,w4,w5] [] [] (by decide +kernel)
def n1318 := cc 7 [w0,w1,w2,w351,w3,w4,w5,w518] [26,179,233] [n1317] (by decide +kernel)
def n1319 := cc 7 [w384,w0,w1,w2,w351,w3,w4,w5] [90,257,635] [n877] (by decide +kernel)
def v499 : Closed T 7 := rotateClosed n1316 auto1 auto1ok
def v500 : Closed T 7 := rotateClosed n878 auto1 auto1ok
def n1320 := cc 8 [w0,w1,w2,w351,w3,w4,w383,w5] [178,315,512,556,635] [n1319,n1318,v499,n1315,v500] (by decide +kernel)
def n1321 := cc 8 [w520,w0,w1,w2,w3,w4,w5] [83,90,178,365,389] [] (by decide +kernel)
def n1322 := cc 7 [w1,w2,w351,w3,w4,w5,w13,w125] [231,351,559,583,647,662] [] (by decide +kernel)
def n1323 := cc 7 [w521,w1,w2,w351,w3,w4,w5,w13] [559,583,634,662] [] (by decide +kernel)
def n1324 := cc 7 [w220,w0,w1,w2,w351,w3,w4,w5] [218,233] [] (by decide +kernel)
def n1325 := cc 7 [w522,w0,w1,w2,w351,w3,w4,w5] [218] [] (by decide +kernel)
def n1326 := cc 8 [w0,w1,w2,w351,w3,w4,w5,w13] [83,90,178,231,556,632,662] [n1323,n1325,n1324,n886,n1318,n885,v342,n1316,v499,n1322,n881,n879,v341] (by decide +kernel)
def v501 : Closed T 8 := rotateClosed n1056 auto1 auto1ok
def v502 : Closed T 8 := rotateClosed n1321 auto1 auto1ok
def v503 : Closed T 8 := rotateClosed n887 auto1 auto1ok
def v504 : Closed T 8 := rotateClosed n1320 auto1 auto1ok
def v505 : Closed T 8 := rotateClosed n889 auto1 auto1ok
def v506 : Closed T 8 := rotateClosed n884 auto1 auto1ok
def n1327 := cc 9 [w0,w1,w2,w351,w3,w4,w5] [178,184,269,556,632] [n1056,v501,n1321,v502,n887,v503,n1320,v504,n1326,n889,v505,n884,v506] (by decide +kernel)
def n1328 := cc 8 [w524,w0,w1,w2,w3,w4,w5] [254,383,676] [] (by decide +kernel)
def n1329 := cc 8 [w0,w1,w2,w3,w4,w385,w13] [231,574,675] [] (by decide +kernel)
def n1330 := cc 8 [w0,w1,w2,w3,w4,w5,w525] [231,351,675] [] (by decide +kernel)
def n1331 := cc 8 [w526,w0,w1,w2,w3,w4,w5] [90,247,589,666] [] (by decide +kernel)
def v507 : Closed T 8 := rotateClosed n1329 auto1 auto1ok
def n1332 := cc 9 [w0,w1,w2,w3,w4,w523,w5] [97,184,459,524,676] [n1331,n1328,n889,n1330,v344,v507] (by decide +kernel)
def n1333 := cc 9 [w0,w1,w350,w8,w4,w5] [184,524,607] [] (by decide +kernel)
def n1334 := cc 7 [w387,w0,w1,w2,w3,w4,w5,w13] [55,58,143,570,579,643] [] (by decide +kernel)
def n1335 := cc 7 [w358,w0,w1,w350,w3,w4,w5,w13] [83,90,570] [] (by decide +kernel)
def n1336 := cc 8 [w0,w1,w350,w2,w3,w4,w5,w13,w125] [83,90,143,231,351,564,581,645,687] [n1335,n1334,n1322] (by decide +kernel)
def n1337 := cc 7 [w0,w1,w527,w2,w3,w4,w5,w13] [58,240,561,582,635] [] (by decide +kernel)
def n1338 := cc 8 [w521,w0,w1,w350,w2,w3,w4,w5,w13] [83,90,143,231,564,581,636,687] [n1323,n1337] (by decide +kernel)
def n1339 := cc 8 [w220,w0,w1,w350,w2,w3,w4,w5] [218,233,675,676,687] [n1324] (by decide +kernel)
def n1340 := cc 7 [w0,w528,w1,w2,w3,w4,w5] [0,218,269,662] [] (by decide +kernel)
def v508 : Closed T 7 := rotateClosed n891 auto1 auto1ok
def n1341 := cc 8 [w352,w0,w1,w2,w3,w4,w5] [97,231,351,662] [n891,v508,n1340] (by decide +kernel)
def n1342 := cc 9 [w0,w1,w350,w2,w3,w4,w5,w13] [83,98,143,231,524,607,687] [n1338,n1341,n1339,n1336,n897,n892,v343,n1326,n1330,n1329,v507] (by decide +kernel)
def v509 : Closed T 9 := rotateClosed n1057 auto1 auto1ok
def v510 : Closed T 9 := rotateClosed n901 auto1 auto1ok
def v511 : Closed T 9 := rotateClosed n1332 auto1 auto1ok
def n1343 := cc 10 [w0,w1,w350,w2,w3,w4,w5] [97,184,269,524,607] [n1057,v509,n901,v510,n1342,n1333,n1327,n1332,v511] (by decide +kernel)
def n1344 := cc 8 [w529,w0,w1,w2,w3,w4,w5] [123,251,378,525,608] [] (by decide +kernel)
def n1345 := cc 9 [w163,w0,w1,w2,w3,w4,w5] [123,179,251,269,524,607,677] [n459,n59,n293,n1344] (by decide +kernel)
def n1346 := cc 8 [w0,w1,w531,w2,w3,w4,w5] [123,208,267,553,630] [] (by decide +kernel)
def n1347 := cc 8 [w0,w530,w1,w531,w2,w3,w4,w5] [123,208,267,553,630] [] (by decide +kernel)
def n1348 := cc 9 [w0,w530,w1,w2,w3,w4,w5] [123,184,267,269,271,524,607] [n59,n1347,n1346] (by decide +kernel)
def n1349 := cc 10 [w0,w1,w2,w3,w8,w4,w5] [97,184,269,524,607] [n460,n60,n622,n1345,n15,n1348,n1333,n294] (by decide +kernel)
def n1350 := cc 9 [w0,w533,w1,w2,w3,w4,w5] [184,524,607] [] (by decide +kernel)
def n1351 := cc 10 [w532,w0,w1,w2,w3,w4,w5] [97,184,524,607] [n1350] (by decide +kernel)
def n1352 := cc 8 [w534,w0,w1,w2,w3,w4,w5] [83,90,179,365,389] [] (by decide +kernel)
def n1353 := cc 8 [w0,w165,w1,w2,w3,w4,w5,w13] [83,90,351,507,662,671] [] (by decide +kernel)
def v512 : Closed T 8 := rotateClosed n1352 auto1 auto1ok
def v513 : Closed T 8 := rotateClosed n902 auto1 auto1ok
def n1354 := cc 9 [w0,w165,w1,w2,w3,w4,w5] [0,208,269,389,655,671,672] [n1352,v512,n461,n1353,n902,v513,n295] (by decide +kernel)
def n1355 := cc 8 [w536,w0,w1,w2,w3,w4,w5] [383,671,676] [] (by decide +kernel)
def n1356 := cc 8 [w0,w1,w2,w3,w4,w537,w15] [179,230,345,517] [] (by decide +kernel)
def n1357 := cc 8 [w0,w1,w2,w3,w4,w537,w13] [351,389,517,521,675] [] (by decide +kernel)
def n1358 := cc 8 [w0,w1,w2,w3,w4,w5,w538] [351,511,675] [] (by decide +kernel)
def n1359 := cc 8 [w539,w0,w1,w2,w3,w4,w5] [374,517,574,666] [] (by decide +kernel)
def v514 : Closed T 8 := rotateClosed n1356 auto1 auto1ok
def v515 : Closed T 8 := rotateClosed n1357 auto1 auto1ok
def n1360 := cc 9 [w0,w1,w2,w3,w4,w535,w5] [97,225,269,459,524,671,676] [n1359,n1355,n902,n1358,v514,v515] (by decide +kernel)
def n1361 := cc 9 [w164,w0,w1,w2,w3,w4,w9,w5] [179,184,269,521,524] [v514] (by decide +kernel)
def n1362 := cc 7 [w0,w1,w2,w541,w3,w4,w5] [320,325,330,511] [] (by decide +kernel)
def n1363 := cc 8 [w0,w1,w2,w540,w3,w4,w5] [97,351,511,550,627] [n1362] (by decide +kernel)
def n1364 := cc 8 [w164,w0,w1,w2,w3,w4,w5,w13,w125] [83,90,645,671,685,687] [] (by decide +kernel)
def n1365 := cc 8 [w164,w220,w0,w1,w2,w3,w4,w5] [356,511,671,687] [] (by decide +kernel)
def n1366 := cc 9 [w164,w0,w1,w2,w3,w4,w5,w13] [83,143,231,351,521,524,607,671,687] [n1365,n1364,n907,n904,v345,n1353,n1363,n1358,n1357,v515] (by decide +kernel)
def v516 : Closed T 9 := rotateClosed n1059 auto1 auto1ok
def v517 : Closed T 9 := rotateClosed n908 auto1 auto1ok
def v518 : Closed T 9 := rotateClosed n1361 auto1 auto1ok
def v519 : Closed T 9 := rotateClosed n1360 auto1 auto1ok
def n1367 := cc 10 [w164,w0,w1,w2,w3,w4,w5] [97,184,269,524,607] [n1059,v516,n462,n296,n908,v517,n1361,v518,n1366,n596,n1354,n1360,v519] (by decide +kernel)
def n1368 := cc 7 [w166,w1,w542,w3,w9,w5] [103,178,179,184,530] [] (by decide +kernel)
def n1369 := cc 7 [w167,w1,w542,w3,w9,w5] [254,512,597,671] [] (by decide +kernel)
def n1370 := cc 7 [w0,w1,w543,w3,w9,w5] [103,178,179,530] [] (by decide +kernel)
def n1371 := cc 7 [w545,w0,w1,w3,w4,w15] [179,258,518,655] [] (by decide +kernel)
def v520 : Closed T 7 := rotateClosed n1371 auto1 auto1ok
def n1372 := cc 8 [w0,w1,w542,w3,w9,w5] [184,524,671,672,675] [v520,n1369,n1368,n1370] (by decide +kernel)
def n1373 := cc 8 [w546,w0,w1,w2,w3,w4,w5] [90,178,438,581] [] (by decide +kernel)
def n1374 := cc 9 [w0,w1,w2,w542,w3,w4,w5] [184,459,524,675] [n1373,v366,n1372] (by decide +kernel)
def n1375 := cc 7 [w548,w0,w2,w3,w4,w299] [102,192,538] [] (by decide +kernel)
def n1376 := cc 7 [w549,w0,w1,w2,w4,w299] [102,196,285,398] [] (by decide +kernel)
def n1377 := cc 7 [w550,w1,w2,w3,w397,w5] [83,106,189,619] [] (by decide +kernel)
def v521 : Closed T 7 := rotateClosed n1375 auto1 auto1ok
def v522 : Closed T 7 := rotateClosed n1376 auto1 auto1ok
def n1378 := cc 8 [w550,w0,w1,w2,w3,w304,w5] [83,106,187,254,617] [v521,v522,n1377,v273,n653] (by decide +kernel)
def v523 : Closed T 7 := rotateClosed n1377 auto1 auto1ok
def n1379 := cc 8 [w0,w1,w2,w3,w4,w299,w551] [90,102,222,258,564] [v523] (by decide +kernel)
def n1380 := cc 6 [w553,w1,w2,w3,w4] [102,178,673] [] (by decide +kernel)
def n1381 := cc 7 [w552,w434,w1,w2,w3,w4] [102,243,518,584] [n1380] (by decide +kernel)
def n1382 := cc 8 [w552,w0,w1,w2,w3,w4,w299] [90,102,241,581] [n1381] (by decide +kernel)
def n1383 := cc 8 [w554,w0,w1,w2,w3,w304,w5] [83,106,254,659] [] (by decide +kernel)
def v524 : Closed T 8 := rotateClosed n1383 auto1 auto1ok
def v525 : Closed T 8 := rotateClosed n1378 auto1 auto1ok
def n1384 := cc 9 [w0,w1,w2,w3,w4,w299] [184,524] [n1382,v524,v525,n1379] (by decide +kernel)
def n1385 := cc 8 [w554,w0,w1,w2,w3,w4,w5] [83,106,254,659] [] (by decide +kernel)
def v526 : Closed T 8 := rotateClosed n1063 auto1 auto1ok
def v527 : Closed T 8 := rotateClosed n949 auto1 auto1ok
def n1386 := cc 9 [w0,w1,w2,w3,w4,w304,w5] [83,97,184,512,607] [v526,n1105,n1385,n730,n950,v527] (by decide +kernel)
def n1387 := cc 9 [w555,w0,w1,w2,w3,w5] [184,459,524] [] (by decide +kernel)
def n1388 := cc 6 [w301,w557,w0,w3,w4] [518,615,668] [] (by decide +kernel)
def n1389 := cc 7 [w557,w0,w300,w3,w4,w15] [108,179,615] [n1388] (by decide +kernel)
def n1390 := cc 6 [w301,w558,w0,w1,w4] [196,518,671] [] (by decide +kernel)
def n1391 := cc 7 [w558,w0,w1,w300,w4,w15] [108,179,196,289] [n1390] (by decide +kernel)
def n1392 := cc 6 [w301,w0,w1,w3,w559] [178,193,518,613] [] (by decide +kernel)
def v528 : Closed T 6 := rotateClosed n1392 auto1 auto1ok
def n1393 := cc 7 [w0,w1,w298,w3,w9,w560] [103,179,531] [v528] (by decide +kernel)
def n1394 := cc 6 [w301,w561,w0,w1,w3] [178,197,512,616] [] (by decide +kernel)
def n1395 := cc 7 [w561,w0,w1,w300,w3,w15] [108,179,197,552] [n1394] (by decide +kernel)
def n1396 := cc 6 [w166,w562,w1,w3,w5] [] [] (by decide +kernel)
def v529 : Closed T 6 := rotateClosed n1396 auto1 auto1ok
def n1397 := cc 7 [w301,w556,w0,w1,w3,w4] [178,192,512,518,612,666] [n1388,n1390,n1394,n1392,v529] (by decide +kernel)
def v530 : Closed T 7 := rotateClosed n1397 auto1 auto1ok
def v531 : Closed T 7 := rotateClosed n1389 auto1 auto1ok
def v532 : Closed T 7 := rotateClosed n1391 auto1 auto1ok
def v533 : Closed T 7 := rotateClosed n1395 auto1 auto1ok
def n1398 := cc 8 [w166,w0,w1,w298,w3,w9,w5] [103,179,184,470,530,664] [v530,v531,v532,v533,n1368,n1393,n1370] (by decide +kernel)
def n1399 := cc 7 [w301,w0,w1,w3,w4,w141] [178,179,222,517,632] [] (by decide +kernel)
def n1400 := cc 6 [w563,w556,w1,w3,w4] [178,195,517,614] [] (by decide +kernel)
def n1401 := cc 7 [w563,w0,w1,w3,w4,w15] [179,222,517,632] [n1400] (by decide +kernel)
def v534 : Closed T 7 := rotateClosed n1399 auto1 auto1ok
def v535 : Closed T 7 := rotateClosed n1401 auto1 auto1ok
def n1402 := cc 8 [w0,w1,w298,w3,w9,w119,w5] [179,214,521,556] [v534,v535] (by decide +kernel)
def n1403 := cc 7 [w0,w1,w565,w3,w9,w5] [83,103,178,577] [] (by decide +kernel)
def n1404 := cc 6 [w567,w1,w300,w3,w4] [108,178,179,517] [] (by decide +kernel)
def n1405 := cc 7 [w566,w174,w1,w300,w3,w4] [179,243,519,644] [n1404] (by decide +kernel)
def n1406 := cc 7 [w566,w301,w0,w1,w3,w4] [178,222,241,517,641] [] (by decide +kernel)
def v536 : Closed T 7 := rotateClosed n1403 auto1 auto1ok
def n1407 := cc 8 [w566,w0,w1,w300,w3,w4,w15] [108,517,641] [n1406,n1405,v536] (by decide +kernel)
def n1408 := cc 7 [w301,w174,w0,w1,w3,w4] [179,258,518,655] [] (by decide +kernel)
def v537 : Closed T 7 := rotateClosed n1408 auto1 auto1ok
def n1409 := cc 8 [w167,w0,w1,w298,w3,w9,w5] [179,254,512,597] [v520,v537,n1369] (by decide +kernel)
def n1410 := cc 6 [w301,w0,w569,w3,w4] [518,615,668] [] (by decide +kernel)
def n1411 := cc 6 [w301,w0,w1,w570,w4] [196,518,671] [] (by decide +kernel)
def n1412 := cc 6 [w301,w0,w1,w3,w571] [178,193,518,613] [] (by decide +kernel)
def n1413 := cc 6 [w301,w0,w1,w572,w3] [178,197,512,616] [] (by decide +kernel)
def n1414 := cc 6 [w568,w573,w1,w3,w4] [178,195,521,614] [] (by decide +kernel)
def n1415 := cc 7 [w568,w301,w0,w1,w3,w4] [178,192,512,518,612,666] [n1414,n1410,n1411,n1413,n1412] (by decide +kernel)
def n1416 := cc 7 [w301,w0,w573,w1,w3,w4] [222,258,512,521,632,676] [n1414] (by decide +kernel)
def n1417 := cc 7 [w545,w301,w0,w1,w3,w4] [258,518,655,672] [] (by decide +kernel)
def n1418 := cc 7 [w301,w574,w0,w1,w3,w4] [178,241,512,521,641,666] [] (by decide +kernel)
def n1419 := cc 5 [w0,w1,w577,w3] [671,678,685] [] (by decide +kernel)
def n1420 := cc 6 [w575,w0,w1,w3,w576] [206,521,671] [n1419] (by decide +kernel)
def n1421 := cc 7 [w575,w301,w0,w1,w3,w4] [204,518,627,671] [n1420] (by decide +kernel)
def n1422 := cc 7 [w301,w0,w1,w3,w4,w576] [231,639,666,672] [n1420] (by decide +kernel)
def n1423 := cc 6 [w578,w0,w1,w579,w3] [250,512,517,593] [n1419] (by decide +kernel)
def n1424 := cc 7 [w578,w430,w0,w1,w3,w5] [247,512,589,675] [n1423] (by decide +kernel)
def v538 : Closed T 6 := rotateClosed n1423 auto1 auto1ok
def n1425 := cc 7 [w301,w0,w1,w580,w3,w4] [247,521,661,671] [v538] (by decide +kernel)
def v539 : Closed T 7 := rotateClosed n1424 auto1 auto1ok
def v540 : Closed T 7 := rotateClosed n1064 auto1 auto1ok
def n1426 := cc 8 [w301,w0,w1,w3,w4] [184,607] [v539,v540,n1417,n1415,n1421,n1106,n1418,n733,n1416,n1425,n1422,n952] (by decide +kernel)
def n1427 := cc 7 [w0,w573,w1,w3,w4,w15] [222,521,671] [v529] (by decide +kernel)
def n1428 := cc 7 [w301,w0,w1,w3,w581,w4] [204,518,627,671] [] (by decide +kernel)
def n1429 := cc 7 [w301,w0,w1,w3,w4,w44] [179,231,247,517,518,639] [] (by decide +kernel)
def n1430 := cc 7 [w582,w301,w0,w1,w3,w4] [179,231,247,512,518,661] [] (by decide +kernel)
def n1431 := cc 7 [w46,w430,w0,w1,w3,w5] [247,512,672] [] (by decide +kernel)
def v541 : Closed T 7 := rotateClosed n1431 auto1 auto1ok
def n1432 := cc 8 [w301,w0,w1,w3,w4,w15] [184,518,521,607,671] [n1406,n1430,v541,n1371,n1408,n1397,n1428,n1399,n1429,n1427] (by decide +kernel)
def n1433 := cc 6 [w583,w0,w1,w3,w581] [179,206,521,629] [] (by decide +kernel)
def n1434 := cc 6 [w585,w0,w1,w298,w3] [179,470,512,629] [] (by decide +kernel)
def v542 : Closed T 6 := rotateClosed n1433 auto1 auto1ok
def n1435 := cc 7 [w0,w1,w298,w3,w584,w44] [179,206,470] [n1434,v542] (by decide +kernel)
def v543 : Closed T 7 := rotateClosed n1428 auto1 auto1ok
def n1436 := cc 8 [w0,w1,w298,w3,w584,w9,w5] [204,550,672] [v543,n1435] (by decide +kernel)
def n1437 := cc 7 [w583,w0,w1,w3,w4,w15] [179,231,517,518,639] [n1433] (by decide +kernel)
def v544 : Closed T 7 := rotateClosed n1429 auto1 auto1ok
def v545 : Closed T 7 := rotateClosed n1437 auto1 auto1ok
def n1438 := cc 8 [w0,w1,w298,w3,w9,w5,w44] [179,231,247,470,574] [v544,v545,n1435] (by decide +kernel)
def v546 : Closed T 6 := rotateClosed n1434 auto1 auto1ok
def n1439 := cc 7 [w582,w586,w0,w1,w300,w3] [179,250,520] [v546] (by decide +kernel)
def v547 : Closed T 7 := rotateClosed n1439 auto1 auto1ok
def n1440 := cc 8 [w46,w0,w1,w298,w3,w9,w5] [247,512,672] [v547,n1431] (by decide +kernel)
def n1441 := cc 7 [w0,w1,w588,w3,w9,w5] [179,470,513,603] [] (by decide +kernel)
def v548 : Closed T 7 := rotateClosed n1441 auto1 auto1ok
def n1442 := cc 8 [w582,w0,w1,w300,w3,w4,w15] [179,247,552] [n1439,n1430,v548] (by decide +kernel)
def v549 : Closed T 8 := rotateClosed n1407 auto1 auto1ok
def v550 : Closed T 8 := rotateClosed n1442 auto1 auto1ok
def v551 : Closed T 8 := rotateClosed n1426 auto1 auto1ok
def v552 : Closed T 8 := rotateClosed n1432 auto1 auto1ok
def v553 : Closed T 8 := rotateClosed n1107 auto1 auto1ok
def v554 : Closed T 8 := rotateClosed n734 auto1 auto1ok
def n1443 := cc 9 [w0,w1,w298,w3,w9,w5] [184,524] [v549,v550,n1065,n1440,v551,v552,v553,n1409,v554,n1398,n1436,n1402,n953,n1438,n1372] (by decide +kernel)
def v555 : Closed T 9 := rotateClosed n1387 auto1 auto1ok
def v556 : Closed T 9 := rotateClosed n1108 auto1 auto1ok
def v557 : Closed T 9 := rotateClosed n735 auto1 auto1ok
def v558 : Closed T 9 := rotateClosed n1386 auto1 auto1ok
def n1444 := cc 10 [w0,w1,w298,w2,w3,w4,w5] [97,184,459,524] [n1066,v555,v556,v557,n954,n1443,n1374,v558,n1384] (by decide +kernel)
def n1445 := cc 8 [w557,w0,w2,w3,w4,w5,w15] [136,518,671] [n1389] (by decide +kernel)
def n1446 := cc 8 [w558,w0,w1,w2,w4,w5,w15] [345,518,671] [n1391] (by decide +kernel)
def n1447 := cc 8 [w0,w1,w2,w3,w4,w9,w560] [127,512,672] [n1393] (by decide +kernel)
def n1448 := cc 8 [w561,w0,w1,w2,w3,w5,w15] [136,197,463,574] [n1395] (by decide +kernel)
def n1449 := cc 7 [w567,w1,w2,w3,w4,w5] [90,136,179,517] [n1404] (by decide +kernel)
def v559 : Closed T 7 := rotateClosed n1449 auto1 auto1ok
def n1450 := cc 8 [w166,w1,w2,w3,w4,w119,w5] [83,127,179,521] [v559] (by decide +kernel)
def v560 : Closed T 8 := rotateClosed n1445 auto1 auto1ok
def v561 : Closed T 8 := rotateClosed n1446 auto1 auto1ok
def v562 : Closed T 8 := rotateClosed n1448 auto1 auto1ok
def n1451 := cc 9 [w166,w0,w1,w2,w3,w4,w9,w5] [127,184,331,512,524,672] [v560,v561,v562,n344,n1398,n1450,n909,n297,n1447] (by decide +kernel)
def n1452 := cc 8 [w0,w168,w1,w2,w3,w4,w119,w5] [127,238,521,685] [] (by decide +kernel)
def n1453 := cc 8 [w0,w140,w1,w2,w3,w4,w9,w5] [127,521,680] [] (by decide +kernel)
def n1454 := cc 8 [w0,w1,w2,w172,w3,w4,w119,w5] [127,303,342,521,556,577] [] (by decide +kernel)
def n1455 := cc 9 [w0,w1,w2,w3,w4,w9,w119,w5] [83,127,179,331,521,556] [v114,n922,n346,n1450,n1227,n1452,n1453,n1402,n1454] (by decide +kernel)
def n1456 := cc 8 [w566,w174,w1,w2,w3,w4,w5] [90,136,179,517] [n1405,n1449] (by decide +kernel)
def n1457 := cc 9 [w566,w0,w1,w2,w3,w4,w5,w15] [90,136,179,182,345,517,641] [n1456,n1407,v131,n436,n1031] (by decide +kernel)
def n1458 := cc 8 [w589,w0,w1,w2,w3,w4,w5] [0,269,502,671] [] (by decide +kernel)
def n1459 := cc 8 [w0,w1,w2,w3,w4,w491,w5] [83,179,247,267,269,503,656] [n1229] (by decide +kernel)
def n1460 := cc 8 [w65,w167,w0,w1,w2,w3,w4,w5] [3,342,521,597,640] [] (by decide +kernel)
def n1461 := cc 8 [w167,w0,w1,w2,w3,w5,w13] [131,459,597,672,676,682] [n1302,n1231] (by decide +kernel)
def n1462 := cc 8 [w70,w167,w0,w1,w2,w3,w5] [73,448,671,672] [] (by decide +kernel)
def v563 : Closed T 8 := rotateClosed n1074 auto1 auto1ok
def v564 : Closed T 8 := rotateClosed n1458 auto1 auto1ok
def v565 : Closed T 8 := rotateClosed n1459 auto1 auto1ok
def n1463 := cc 9 [w167,w0,w1,w2,w3,w4,w5] [127,184,254,269,389,448,459,512,597,672,676] [n963,v563,n1303,n1460,n1462,n463,n61,n624,n1232,n1461,n312,n921,n346,v564,v565,n191] (by decide +kernel)
def v566 : Closed T 8 := rotateClosed n1456 auto1 auto1ok
def n1464 := cc 9 [w167,w0,w1,w2,w3,w4,w9,w5] [97,184,389,672,678] [v566,n1409,n346,n910,n298] (by decide +kernel)
def n1465 := cc 7 [w0,w1,w399,w2,w3,w4,w5,w590] [90,127,682] [] (by decide +kernel)
def n1466 := cc 6 [w400,w0,w1,w399,w2,w3,w13] [130,268] [] (by decide +kernel)
def n1467 := cc 7 [w400,w0,w1,w399,w2,w3,w4,w5] [90,267,477] [n1466,n955] (by decide +kernel)
def n1468 := cc 7 [w0,w1,w399,w2,w3,w5,w13] [131,217,405,459,682] [n1466,n956] (by decide +kernel)
def n1469 := cc 8 [w0,w1,w399,w2,w3,w4,w5] [90,127,214,267,303,405,477,541] [n1467,n1238,n1465,n1468,n957] (by decide +kernel)
def n1470 := cc 8 [w0,w168,w1,w399,w2,w3,w4,w5] [127,179,238,682] [] (by decide +kernel)
def n1471 := cc 8 [w0,w1,w2,w3,w4,w591,w5] [231,269,624,676] [] (by decide +kernel)
def n1472 := cc 8 [w0,w168,w1,w2,w3,w5,w13] [231,389,459,676,682] [n958,n1468] (by decide +kernel)
def v567 : Closed T 8 := rotateClosed n1160 auto1 auto1ok
def v568 : Closed T 8 := rotateClosed n1471 auto1 auto1ok
def n1473 := cc 9 [w0,w168,w1,w2,w3,w4,w5] [0,127,184,331,389,459,682] [v567,n1301,n61,n1239,n1470,n959,n1472,n1469,v568] (by decide +kernel)
def n1474 := cc 8 [w0,w1,w399,w2,w3,w4,w9,w5] [214,672,685] [] (by decide +kernel)
def n1475 := cc 8 [w0,w1,w2,w3,w4,w591,w5,w15] [51,345,518,666,671] [] (by decide +kernel)
def n1476 := cc 8 [w0,w168,w1,w2,w3,w9,w5,w13] [487,672,685] [] (by decide +kernel)
def n1477 := cc 8 [w0,w168,w1,w2,w3,w4,w5,w44] [179,487,685] [] (by decide +kernel)
def v569 : Closed T 8 := rotateClosed n1475 auto1 auto1ok
def n1478 := cc 9 [w0,w168,w1,w2,w3,w4,w9,w5] [127,184,487,672,685] [v567,n1452,n1477,n911,n1476,n299,n1474,v569] (by decide +kernel)
def n1479 := cc 9 [w40,w0,w1,w2,w3,w4,w5,w15] [179,184,345,459,517,648] [n1160] (by decide +kernel)
def n1480 := cc 7 [w0,w1,w2,w226,w3,w9,w15,w13] [232,262,264,336,574] [] (by decide +kernel)
def n1481 := cc 8 [w0,w1,w2,w3,w9,w15,w13] [86,180,231,389,574] [n1480] (by decide +kernel)
def n1482 := cc 7 [w46,w586,w0,w1,w2,w3] [83,90,179,250] [] (by decide +kernel)
def n1483 := cc 8 [w46,w0,w1,w2,w3,w4,w15] [83,90,179,247,592] [n1482] (by decide +kernel)
def n1484 := cc 8 [w0,w1,w2,w3,w4,w5,w44] [0,90,179,269,427] [] (by decide +kernel)
def v570 : Closed T 8 := rotateClosed n1483 auto1 auto1ok
def n1485 := cc 9 [w0,w1,w2,w3,w4,w9,w5,w15] [179,184,331,345,389,459,517,521,639] [n1483,v570,n1484,n1481] (by decide +kernel)
def n1486 := cc 8 [w0,w1,w2,w3,w4,w406,w15] [81,90,179,184,427] [] (by decide +kernel)
def n1487 := cc 8 [w179,w0,w1,w2,w3,w15,w13] [180,231,518,574] [] (by decide +kernel)
def n1488 := cc 8 [w46,w181,w0,w1,w2,w3,w4] [179,247,512] [] (by decide +kernel)
def v571 : Closed T 8 := rotateClosed n1488 auto1 auto1ok
def n1489 := cc 9 [w179,w0,w1,w2,w3,w4,w5,w15] [179,184,427,459,521,574] [v571,n1487,n1484,n1486] (by decide +kernel)
def n1490 := cc 8 [w0,w1,w2,w3,w592,w4,w9,w5] [331,512,556,672] [] (by decide +kernel)
def n1491 := cc 7 [w0,w1,w2,w3,w9,w593,w13] [337,512,672] [] (by decide +kernel)
def n1492 := cc 8 [w0,w1,w2,w3,w4,w9,w5,w593] [331,512,574,672] [n1491] (by decide +kernel)
def n1493 := cc 8 [w0,w1,w2,w172,w3,w9,w5,w13] [337,512,639,672] [n1491] (by decide +kernel)
def n1494 := cc 8 [w0,w1,w2,w172,w3,w4,w5,w44] [83,179,339,639] [] (by decide +kernel)
def n1495 := cc 9 [w0,w1,w2,w172,w3,w4,w9,w5] [182,331,512,524,639,672] [n1454,n1494,n915,n1493,n1490,n1492,n304] (by decide +kernel)
def n1496 := cc 9 [w594,w0,w1,w2,w3,w4,w5,w15] [179,345,517,607] [n1356] (by decide +kernel)
def n1497 := cc 8 [w0,w1,w2,w3,w4,w15,w61] [90,184,345,671] [] (by decide +kernel)
def n1498 := cc 8 [w0,w1,w2,w3,w4,w595,w5] [179,487,574] [] (by decide +kernel)
def n1499 := cc 8 [w596,w0,w1,w2,w3,w4,w5] [331,487,512,521,666] [] (by decide +kernel)
def v572 : Closed T 8 := rotateClosed n1499 auto1 auto1ok
def v573 : Closed T 8 := rotateClosed n1498 auto1 auto1ok
def n1500 := cc 9 [w0,w1,w2,w60,w3,w4,w5,w15] [345,607,671] [v572,v573,n1497] (by decide +kernel)
def n1501 := cc 9 [w65,w0,w1,w2,w3,w4,w9,w5] [159,245,331,524,639,672] [n520,n1460,n352,n914,n305] (by decide +kernel)
def n1502 := cc 8 [w220,w0,w1,w2,w3,w4,w15] [137,184,602,671,675] [n1240] (by decide +kernel)
def v574 : Closed T 7 := rotateClosed n1304 auto1 auto1ok
def n1503 := cc 8 [w0,w134,w1,w2,w3,w4,w15,w13] [231,459,675,687] [v574] (by decide +kernel)
def n1504 := cc 8 [w0,w1,w414,w3,w4,w15,w13] [231,627,662,675] [] (by decide +kernel)
def n1505 := cc 8 [w47,w0,w1,w3,w4,w15,w13] [184,661,671,684] [] (by decide +kernel)
def n1506 := cc 8 [w0,w1,w2,w226,w3,w4,w15,w13] [231,348,574,589,607,662,675] [n1480] (by decide +kernel)
def n1507 := cc 8 [w0,w1,w2,w3,w581,w15,w13] [90,427,574,671] [] (by decide +kernel)
def n1508 := cc 8 [w46,w0,w1,w2,w3,w9,w13] [83,459,672,678] [] (by decide +kernel)
def v575 : Closed T 8 := rotateClosed n1305 auto1 auto1ok
def v576 : Closed T 8 := rotateClosed n1508 auto1 auto1ok
def v577 : Closed T 8 := rotateClosed n1461 auto1 auto1ok
def v578 : Closed T 8 := rotateClosed n1476 auto1 auto1ok
def v579 : Closed T 8 := rotateClosed n1472 auto1 auto1ok
def v580 : Closed T 8 := rotateClosed n1493 auto1 auto1ok
def n1509 := cc 9 [w0,w1,w2,w3,w4,w15,w13] [184,231,389,427,574,607,671,675] [n1163,v575,v576,n1487,n1505,n62,n521,n625,n1110,v577,n1502,n1243,n1292,v578,v579,n1503,n1504,v580,n1506,n1507,n916,n354,n961,n1481,n307] (by decide +kernel)
def n1510 := cc 7 [w46,w47,w0,w1,w3,w4] [90,179,447] [] (by decide +kernel)
def n1511 := cc 8 [w47,w0,w1,w3,w4,w9,w5] [83,90,179,455,603] [n1510] (by decide +kernel)
def n1512 := cc 8 [w46,w0,w1,w2,w3,w4,w13] [445,512,589,675] [n1510] (by decide +kernel)
def n1513 := cc 9 [w0,w1,w2,w3,w4,w9,w5,w13] [184,389,459,517,524,676] [n1512,n1511,n1484] (by decide +kernel)
def n1514 := cc 8 [w0,w417,w1,w2,w3,w9,w5] [389,666,671] [] (by decide +kernel)
def n1515 := cc 8 [w0,w1,w2,w3,w597,w4,w15] [459,512,521,607] [] (by decide +kernel)
def n1516 := cc 8 [w0,w1,w2,w3,w4,w15,w13] [52,90,231,389,671] [] (by decide +kernel)
def v581 : Closed T 8 := rotateClosed n1515 auto1 auto1ok
def v582 : Closed T 8 := rotateClosed n1516 auto1 auto1ok
def n1517 := cc 9 [w70,w0,w1,w2,w3,w9,w5] [184,389,459,524,672] [n522,n1462,n355,n308,n1514,v581,v582] (by decide +kernel)
def n1518 := cc 8 [w0,w1,w229,w3,w4,w5,w15] [179,427,487] [] (by decide +kernel)
def n1519 := cc 8 [w70,w586,w0,w1,w2,w3,w5] [90,427,517,518,574] [] (by decide +kernel)
def n1520 := cc 9 [w70,w0,w1,w2,w3,w4,w5,w15] [184,459,574,671] [n1519,n1484,n1516,n1518] (by decide +kernel)
def n1521 := cc 8 [w46,w0,w1,w2,w3,w4,w5] [50,90,247,343,445,521,666] [] (by decide +kernel)
def n1522 := cc 7 [w585,w0,w1,w2,w3,w4] [83,179,487,639] [n1434] (by decide +kernel)
def v583 : Closed T 7 := rotateClosed n1522 auto1 auto1ok
def v584 : Closed T 7 := rotateClosed n1435 auto1 auto1ok
def n1523 := cc 8 [w0,w1,w2,w3,w581,w5,w44] [90,179,427] [v583,v584] (by decide +kernel)
def v585 : Closed T 8 := rotateClosed n1521 auto1 auto1ok
def v586 : Closed T 8 := rotateClosed n1436 auto1 auto1ok
def n1524 := cc 9 [w0,w1,w2,w3,w581,w4,w5,w15] [184,427,459,518,574,671] [v585,v586,n1523,n1507] (by decide +kernel)
def n1525 := cc 8 [w45,w0,w1,w2,w3,w4,w5] [83,90,179,267,269,428,640] [n64,n628,n1244] (by decide +kernel)
def n1526 := cc 7 [w0,w1,w598,w2,w3,w4,w5] [83,132,134,146,267] [] (by decide +kernel)
def n1527 := cc 8 [w0,w496,w1,w2,w3,w4,w5] [97,231,267,427,487] [n1526] (by decide +kernel)
def n1528 := cc 8 [w0,w496,w1,w2,w3,w4,w5,w44] [90,179,339,427,575] [n1248] (by decide +kernel)
def n1529 := cc 8 [w47,w0,w1,w2,w3,w4,w5] [0,179,269,455,508] [] (by decide +kernel)
def v587 : Closed T 7 := rotateClosed n1510 auto1 auto1ok
def n1530 := cc 8 [w47,w0,w1,w3,w4,w5,w44] [0,179,684] [n1510,v587] (by decide +kernel)
def n1531 := cc 8 [w0,w1,w2,w599,w3,w4,w5,w44] [90,179,339,574] [] (by decide +kernel)
def n1532 := cc 8 [w46,w0,w1,w2,w3,w4,w44] [0,179,678] [n1482,n1510] (by decide +kernel)
def v588 : Closed T 8 := rotateClosed n1532 auto1 auto1ok
def v589 : Closed T 8 := rotateClosed n1101 auto1 auto1ok
def n1533 := cc 9 [w0,w1,w2,w3,w4,w5,w44] [83,90,97,179,231,269,427,639] [n1162,n1521,v585,n1532,v588,n1529,n1530,n65,n523,n629,n1101,v589,n1525,n1249,n1527,n1528,n1531,n357,n918,v372,n309] (by decide +kernel)
def n1534 := cc 8 [w0,w496,w1,w2,w3,w4,w9,w5] [179,487,680] [] (by decide +kernel)
def v590 : Closed T 8 := rotateClosed n1523 auto1 auto1ok
def n1535 := cc 9 [w0,w1,w2,w3,w4,w9,w5,w44] [83,90,179,331,487,512,517,639] [v570,n1532,n1511,n1251,n1477,n1534,n1438,n1494,v590] (by decide +kernel)
def n1536 := cc 8 [w0,w479,w1,w2,w3,w4,w5] [134,267,269,590,666,672] [n1252] (by decide +kernel)
def n1537 := cc 8 [w0,w600,w1,w2,w3,w4,w5] [267,500,671] [] (by decide +kernel)
def v591 : Closed T 8 := rotateClosed n1519 auto1 auto1ok
def v592 : Closed T 8 := rotateClosed n1537 auto1 auto1ok
def n1538 := cc 9 [w46,w0,w1,w2,w3,w4,w5] [90,97,184,247,269,389,445,639,666,672] [n963,n1301,v591,n1488,n66,n524,n630,n1102,n1253,n1483,n1512,n1532,n919,n310,n1536,v592,n1484] (by decide +kernel)
def n1539 := cc 8 [w582,w586,w0,w1,w2,w3,w5] [90,179,427,517] [n1439,v583] (by decide +kernel)
def v593 : Closed T 8 := rotateClosed n1539 auto1 auto1ok
def n1540 := cc 9 [w46,w0,w1,w2,w3,w4,w9,w5] [184,389,459,672,678] [v593,n1440,n1532,n1508] (by decide +kernel)
def n1541 := cc 9 [w582,w0,w1,w2,w3,w4,w5,w15] [90,179,427,574] [n1539,n1442,n1484,n1486,n1518] (by decide +kernel)
def v594 : Closed T 9 := rotateClosed n1457 auto1 auto1ok
def v595 : Closed T 9 := rotateClosed n1479 auto1 auto1ok
def v596 : Closed T 9 := rotateClosed n1496 auto1 auto1ok
def v597 : Closed T 9 := rotateClosed n1541 auto1 auto1ok
def v598 : Closed T 9 := rotateClosed n1075 auto1 auto1ok
def v599 : Closed T 9 := rotateClosed n1520 auto1 auto1ok
def v600 : Closed T 9 := rotateClosed n1489 auto1 auto1ok
def v601 : Closed T 9 := rotateClosed n1111 auto1 auto1ok
def v602 : Closed T 9 := rotateClosed n737 auto1 auto1ok
def v603 : Closed T 9 := rotateClosed n1293 auto1 auto1ok
def v604 : Closed T 9 := rotateClosed n1500 auto1 auto1ok
def v605 : Closed T 9 := rotateClosed n1524 auto1 auto1ok
def v606 : Closed T 9 := rotateClosed n964 auto1 auto1ok
def v607 : Closed T 9 := rotateClosed n1509 auto1 auto1ok
def n1542 := cc 10 [w0,w1,w2,w3,w4,w9,w5] [97,184,269,389,459,524] [v594,v447,v595,v596,v597,n1068,v598,n1306,n1501,v599,n1517,n1540,n1538,n464,n1361,v600,n67,n525,n631,v601,n1103,n1464,n1463,n17,n578,v602,n1451,n1254,v603,n1478,n1473,n1443,n315,v604,n1495,v605,n923,v606,n1455,n1485,n1513,n1535,n359,n1533,v408,v607,n311] (by decide +kernel)
def n1543 := cc 8 [w602,w0,w1,w2,w3,w4,w5] [83,90,178,241,269,562] [] (by decide +kernel)
def n1544 := cc 8 [w65,w0,w601,w1,w2,w3,w4,w5] [245,368,556,652] [] (by decide +kernel)
def v608 : Closed T 8 := rotateClosed n1543 auto1 auto1ok
def v609 : Closed T 8 := rotateClosed n1544 auto1 auto1ok
def n1545 := cc 9 [w0,w292,w1,w2,w3,w4,w5] [184,269,389,521,632,675] [n1076,v608,n336,v609,n633,n966,v131,n924] (by decide +kernel)
def n1546 := cc 8 [w603,w0,w1,w2,w3,w4,w5] [254,512,672] [] (by decide +kernel)
def n1547 := cc 8 [w0,w1,w2,w3,w4,w403,w13] [231,389,666,671] [] (by decide +kernel)
def n1548 := cc 8 [w70,w0,w1,w2,w3,w177,w5] [487,512,521,589,666] [] (by decide +kernel)
def v610 : Closed T 8 := rotateClosed n1547 auto1 auto1ok
def n1549 := cc 9 [w0,w1,w2,w3,w4,w177,w5] [83,97,184,269,389,589,664,672] [n1548,n1521,n634,n1113,n1546,n966,n1484,v374,v610,n317] (by decide +kernel)
def n1550 := cc 9 [w0,w1,w2,w3,w4,w9,w5] [43,97,184,331,389,459,672] [n1521,n344,n191,n1484,v357,v582,n318] (by decide +kernel)
def v611 : Closed T 8 := rotateClosed n1070 auto1 auto1ok
def n1551 := cc 9 [w118,w181,w0,w1,w3,w4] [184,607] [v611,n1114,n741,n968,n1426] (by decide +kernel)
def n1552 := cc 8 [w0,w1,w2,w604,w3,w4,w5] [369,512,521] [] (by decide +kernel)
def n1553 := cc 7 [w118,w605,w0,w1,w3,w4] [179,199,373] [] (by decide +kernel)
def n1554 := cc 8 [w118,w0,w1,w2,w3,w4,w61] [199,369,675] [n1553] (by decide +kernel)
def n1555 := cc 9 [w118,w0,w1,w2,w60,w3,w4,w5] [198,269,607,675] [n1554,n1552] (by decide +kernel)
def n1556 := cc 9 [w118,w178,w0,w1,w2,w3,w4,w5] [158,244,369,589,607] [n319,v609] (by decide +kernel)
def n1557 := cc 8 [w118,w47,w0,w1,w3,w4,w5] [231,593,672] [] (by decide +kernel)
def n1558 := cc 9 [w118,w0,w1,w2,w3,w4,w5,w13] [231,389,607,675] [n1557,n1484,v610,n1516] (by decide +kernel)
def n1559 := cc 8 [w118,w0,w1,w229,w3,w4,w5] [487,512,521,589,666] [] (by decide +kernel)
def n1560 := cc 9 [w118,w70,w0,w1,w2,w3,w4,w5] [247,459,589,675] [n1559,n1548,n1521] (by decide +kernel)
def v612 : Closed T 9 := rotateClosed n1071 auto1 auto1ok
def v613 : Closed T 9 := rotateClosed n1550 auto1 auto1ok
def n1561 := cc 10 [w118,w0,w1,w2,w3,w4,w5] [97,184,269,389,607] [n1077,v612,n1560,n1556,n1551,n635,n1115,n580,n742,n1555,n969,n927,n1558,n320,n1545,n1549,v613] (by decide +kernel)
def n1562 := cc 8 [w606,w0,w1,w2,w3,w4,w5] [90,179,438,581] [] (by decide +kernel)
def n1563 := cc 8 [w0,w180,w1,w2,w3,w5,w13] [389,459,524,662,672] [] (by decide +kernel)
def n1564 := cc 9 [w0,w180,w1,w2,w3,w4,w5] [97,389,459,524,672] [n1562,n465,n349,n1563,v377,n191,n321] (by decide +kernel)
def n1565 := cc 8 [w607,w0,w1,w2,w3,w4,w5] [83,179,233,505,659] [] (by decide +kernel)
def n1566 := cc 8 [w179,w0,w1,w2,w3,w393,w5] [179,469,508,603] [] (by decide +kernel)
def v614 : Closed T 8 := rotateClosed n970 auto1 auto1ok
def v615 : Closed T 8 := rotateClosed n1486 auto1 auto1ok
def n1567 := cc 9 [w0,w1,w2,w3,w4,w393,w5] [83,97,231,459,517,607] [n1566,n1529,n1117,n1565,n929,n971,n1484,v614,v615] (by decide +kernel)
def n1568 := cc 8 [w179,w181,w0,w1,w2,w3,w13] [180,231,401,469,603] [] (by decide +kernel)
def v616 : Closed T 8 := rotateClosed n1566 auto1 auto1ok
def n1569 := cc 9 [w179,w181,w0,w1,w2,w3,w4,w5] [179,184,455,508,603] [n1568,n1566,v616,n1529] (by decide +kernel)
def n1570 := cc 8 [w0,w1,w2,w608,w3,w4,w13] [459,512,550,666] [] (by decide +kernel)
def n1571 := cc 8 [w179,w220,w0,w1,w2,w3,w5] [452,662,672] [] (by decide +kernel)
def v617 : Closed T 8 := rotateClosed n1570 auto1 auto1ok
def n1572 := cc 9 [w179,w0,w1,w2,w3,w5,w13] [231,389,459,521,524,662,664] [n1568,n1118,n1571,n930,n973,n1487,n1563,v617,v582] (by decide +kernel)
def v618 : Closed T 9 := rotateClosed n1551 auto1 auto1ok
def v619 : Closed T 9 := rotateClosed n1567 auto1 auto1ok
def n1573 := cc 10 [w179,w0,w1,w2,w3,w4,w5] [97,184,389,459,524] [n1073,v618,n466,n1569,n1119,n744,n323,n974,n1489,n932,n1572,n1564,v619,n1550] (by decide +kernel)
def n1574 := cc 8 [w609,w0,w1,w2,w3,w4,w5] [90,179,360,431,459] [] (by decide +kernel)
def n1575 := cc 8 [w610,w0,w1,w2,w3,w4,w5] [90,179,182,184,438] [] (by decide +kernel)
def n1576 := cc 9 [w0,w1,w2,w3,w199,w4,w5] [184,269,389,636,671,675] [n1575,n468,n1574,n373,v379,n371] (by decide +kernel)
def n1577 := cc 8 [w611,w0,w1,w2,w3,w4,w5] [90,179,377,448,459] [] (by decide +kernel)
def n1578 := cc 8 [w612,w0,w1,w2,w3,w4,w5] [369,512,521] [] (by decide +kernel)
def n1579 := cc 9 [w0,w1,w2,w3,w200,w4,w5] [97,269,389,459,672] [n1578,n527,n1577,n373,v573,n372] (by decide +kernel)
def n1580 := cc 7 [w614,w0,w2,w3,w4,w61] [111,281,662] [] (by decide +kernel)
def n1581 := cc 7 [w0,w1,w616,w3,w100,w5] [115,279,521] [] (by decide +kernel)
def n1582 := cc 7 [w617,w0,w1,w3,w4,w61] [111,199,282,397] [] (by decide +kernel)
def n1583 := cc 7 [w615,w1,w2,w3,w411,w5] [83,115,280,466] [] (by decide +kernel)
def v620 : Closed T 7 := rotateClosed n1580 auto1 auto1ok
def v621 : Closed T 7 := rotateClosed n1582 auto1 auto1ok
def n1584 := cc 8 [w615,w0,w1,w2,w3,w100,w5] [115,202,278,459,521,524,662] [v620,v621,n1583,n1581] (by decide +kernel)
def n1585 := cc 8 [w0,w1,w2,w3,w4,w61,w618] [90,199,327,385,420,671] [] (by decide +kernel)
def n1586 := cc 7 [w619,w439,w1,w2,w3,w4] [111,366,662] [] (by decide +kernel)
def n1587 := cc 8 [w619,w0,w1,w2,w3,w4,w61] [90,111,199,365,438,517] [n1586] (by decide +kernel)
def n1588 := cc 8 [w620,w0,w1,w2,w3,w100,w5] [83,202,383,662,672] [] (by decide +kernel)
def n1589 := cc 7 [w0,w1,w2,w622,w3,w100,w5] [284,662,672] [] (by decide +kernel)
def n1590 := cc 6 [w625,w0,w1,w3,w4] [671,677] [] (by decide +kernel)
def v622 : Closed T 6 := rotateClosed n1590 auto1 auto1ok
def n1591 := cc 7 [w0,w1,w621,w3,w595,w5] [202,286,672] [v622] (by decide +kernel)
def n1592 := cc 8 [w0,w1,w621,w2,w3,w100,w5] [115,202,283,459,524,662] [n1591,n1589] (by decide +kernel)
def v623 : Closed T 7 := rotateClosed n1591 auto1 auto1ok
def n1593 := cc 8 [w0,w1,w2,w3,w4,w61,w624] [90,345,671] [v623] (by decide +kernel)
def n1594 := cc 7 [w626,w605,w0,w1,w3,w4] [199,373,517] [n1590] (by decide +kernel)
def n1595 := cc 8 [w626,w0,w1,w2,w3,w4,w61] [199,369,675] [n1594] (by decide +kernel)
def v624 : Closed T 7 := rotateClosed n1594 auto1 auto1ok
def n1596 := cc 8 [w627,w0,w1,w2,w3,w100,w5] [388,662,672] [v624] (by decide +kernel)
def v625 : Closed T 8 := rotateClosed n1596 auto1 auto1ok
def v626 : Closed T 8 := rotateClosed n1588 auto1 auto1ok
def v627 : Closed T 8 := rotateClosed n1584 auto1 auto1ok
def v628 : Closed T 8 := rotateClosed n1592 auto1 auto1ok
def n1597 := cc 9 [w0,w1,w2,w3,w4,w61] [269,389] [n1587,n1595,n469,v625,n528,v626,n147,v627,v628,n375,n1585,n1593] (by decide +kernel)
def n1598 := cc 8 [w620,w0,w1,w2,w3,w4,w5] [83,184,383,662,672] [] (by decide +kernel)
def v629 : Closed T 7 := rotateClosed n1553 auto1 auto1ok
def n1599 := cc 8 [w627,w0,w1,w2,w3,w4,w5] [179,508,603] [v629] (by decide +kernel)
def v630 : Closed T 8 := rotateClosed n1080 auto1 auto1ok
def v631 : Closed T 8 := rotateClosed n1554 auto1 auto1ok
def v632 : Closed T 8 := rotateClosed n977 auto1 auto1ok
def v633 : Closed T 8 := rotateClosed n1497 auto1 auto1ok
def n1600 := cc 9 [w0,w1,w2,w3,w4,w100,w5] [97,184,459,524,662,676] [v630,v631,n1599,n529,n1598,n376,n978,n1498,v632,v633] (by decide +kernel)
def n1601 := cc 9 [w63,w0,w1,w2,w3,w5] [269,389,459] [n470,n530,n149,n377] (by decide +kernel)
def n1602 := cc 8 [w64,w0,w1,w2,w4] [269,524,607] [n471,n531,n151,n378] (by decide +kernel)
def v634 : Closed T 8 := rotateClosed n1602 auto1 auto1ok
def n1603 := cc 9 [w0,w1,w2,w60,w12,w5] [269,607] [v634,n472,n532,n152,n379] (by decide +kernel)
def v635 : Closed T 9 := rotateClosed n1601 auto1 auto1ok
def v636 : Closed T 9 := rotateClosed n1600 auto1 auto1ok
def n1604 := cc 10 [w0,w1,w2,w60,w3,w4,w5] [97,184,269,389,607] [n1081,n1555,v635,n473,n533,n153,n380,n980,n1500,n1603,n1576,n1579,v636,n1597] (by decide +kernel)
def n1605 := cc 8 [w629,w0,w1,w2,w3,w4,w5] [179,183,184,504,525] [] (by decide +kernel)
def n1606 := cc 8 [w0,w1,w2,w630,w3,w4,w5] [179,267,367,451,641] [] (by decide +kernel)
def v637 : Closed T 8 := rotateClosed n1605 auto1 auto1ok
def n1607 := cc 9 [w203,w0,w1,w2,w3,w4,w5] [138,183,184,524,607,681] [n392,n1166,n68,n535,n1145,n381,v637,n1606] (by decide +kernel)
def n1608 := cc 6 [w631,w1,w205,w2,w3,w4,w5] [179] [] (by decide +kernel)
def n1609 := cc 6 [w209,w0,w1,w205,w2,w3,w4] [] [] (by decide +kernel)
def n1610 := cc 7 [w0,w1,w205,w2,w208,w3,w4,w5] [19,179,211,676] [n1609,n1608] (by decide +kernel)
def n1611 := cc 7 [w206,w0,w1,w205,w2,w3,w4,w5] [179,211,267] [n382] (by decide +kernel)
def n1612 := cc 8 [w0,w1,w205,w2,w3,w4,w5] [138,179,211,267,415,630] [n1611,n1610,n383] (by decide +kernel)
def n1613 := cc 7 [w0,w1,w205,w2,w207,w3,w4,w5] [25,138,179,225,317,318] [n1608,n384] (by decide +kernel)
def n1614 := cc 7 [w206,w0,w204,w1,w2,w3,w4,w5] [10,61,179,211] [] (by decide +kernel)
def n1615 := cc 8 [w0,w204,w1,w205,w2,w3,w4,w5] [138,211,225,267,363,630] [n1614,n388,n1613,n385] (by decide +kernel)
def n1616 := cc 8 [w0,w1,w2,w207,w3,w4,w5] [179,332,425,638] [] (by decide +kernel)
def n1617 := cc 7 [w631,w0,w204,w1,w2,w3,w4,w5] [25,74,125,138] [n1608] (by decide +kernel)
def n1618 := cc 8 [w0,w204,w1,w2,w207,w3,w4,w5] [125,138,225,267,331,367,638] [n1617,n388,n386,n1613] (by decide +kernel)
def n1619 := cc 9 [w0,w204,w1,w2,w3,w4,w5] [138,225,267,269,270,271,389,607] [n1165,n68,n1615,n390,n1618,n1612,n1616] (by decide +kernel)
def n1620 := cc 8 [w0,w632,w1,w2,w3,w4,w5] [97,179,267,597,655] [] (by decide +kernel)
def n1621 := cc 8 [w0,w634,w1,w2,w3,w4,w5] [230,267,540,683] [] (by decide +kernel)
def v638 : Closed T 8 := rotateClosed n1621 auto1 auto1ok
def n1622 := cc 9 [w55,w0,w1,w2,w3,w4,w5] [97,179,225,511,524,607] [n392,n1165,n69,n636,n1620,v638] (by decide +kernel)
def n1623 := cc 10 [w0,w1,w2,w3,w4,w12,w5] [97,184,389,524,607] [n475,n1167,n1622,n70,n536,n637,n1607,n19,n155,n1147,n1619,n393,n1603] (by decide +kernel)
def n1624 := cc 9 [w65,w66,w0,w1,w2,w4] [269,524] [n476,n537,n157,n394,n1602] (by decide +kernel)
def v639 : Closed T 9 := rotateClosed n1082 auto1 auto1ok
def v640 : Closed T 9 := rotateClosed n1556 auto1 auto1ok
def n1625 := cc 10 [w65,w0,w1,w2,w3,w4,w5] [269,524,607] [v639,v640,n1624,n477,n538,n158,n395,n981,n1501] (by decide +kernel)
def n1626 := cc 8 [w636,w0,w1,w2,w3,w4,w5] [179,431,641] [] (by decide +kernel)
def n1627 := cc 9 [w0,w635,w1,w2,w3,w4,w5] [184,389,607,671] [n1626,n397] (by decide +kernel)
def n1628 := cc 8 [w637,w0,w1,w2,w3,w4,w5] [179,448,655] [] (by decide +kernel)
def n1629 := cc 9 [w0,w1,w2,w214,w3,w4,w5] [97,179,389,607] [n540,n1628,n397,n396] (by decide +kernel)
def v641 : Closed T 9 := rotateClosed n1624 auto1 auto1ok
def n1630 := cc 10 [w67,w0,w1,w2,w3,w4,w5] [97,184,389,607] [v641,n479,n541,n160,n399,n1627,n1629] (by decide +kernel)
def n1631 := cc 7 [w639,w0,w1,w2,w3,w13] [180,431,577,662] [] (by decide +kernel)
def n1632 := cc 8 [w639,w0,w1,w2,w3,w4,w5] [179,431,491,577] [n1631] (by decide +kernel)
def n1633 := cc 7 [w413,w1,w2,w3,w638,w13] [389,535,662,669] [] (by decide +kernel)
def n1634 := cc 7 [w220,w1,w2,w3,w638,w13] [452,601,662,669,671] [] (by decide +kernel)
def n1635 := cc 6 [w0,w1,w2,w3,w640,w13] [53,180,205,516] [] (by decide +kernel)
def n1636 := cc 7 [w0,w1,w414,w2,w3,w638,w13] [17,55,205,291,662,671] [n1635] (by decide +kernel)
def n1637 := cc 7 [w0,w1,w2,w3,w641,w13] [121,180,535,662] [] (by decide +kernel)
def n1638 := cc 7 [w642,w0,w1,w2,w3,w13] [420,452,601,662,671] [] (by decide +kernel)
def n1639 := cc 8 [w0,w1,w2,w3,w638,w13] [389,524,671,675] [n1638,n1631,n1634,n1633,n1636,n1637,n402] (by decide +kernel)
def n1640 := cc 9 [w0,w1,w2,w3,w4,w638,w5] [184,389,459,524,671] [n1632,n403,n1639] (by decide +kernel)
def n1641 := cc 7 [w643,w0,w1,w2,w3,w13] [180,448,512,597] [] (by decide +kernel)
def n1642 := cc 8 [w643,w0,w1,w2,w3,w4,w5] [179,448,502,597] [n1641] (by decide +kernel)
def n1643 := cc 7 [w0,w1,w2,w3,w217,w13,w125] [86,180,206,420,564] [] (by decide +kernel)
def n1644 := cc 7 [w220,w0,w1,w2,w3,w217,w13] [180,452,601,662] [] (by decide +kernel)
def n1645 := cc 6 [w0,w1,w644,w3,w217,w13] [180,206,516,551] [] (by decide +kernel)
def n1646 := cc 7 [w0,w1,w414,w3,w217,w13] [180,206,445,550,662] [n1645] (by decide +kernel)
def n1647 := cc 7 [w47,w0,w1,w3,w217,w13] [180,206,455,603] [] (by decide +kernel)
def n1648 := cc 7 [w0,w1,w2,w3,w645,w13] [206,550,662] [n1635] (by decide +kernel)
def n1649 := cc 7 [w646,w0,w1,w2,w3,w13] [180,206,455,603] [] (by decide +kernel)
def n1650 := cc 8 [w0,w1,w2,w3,w217,w13] [180,389,512,524] [n1649,n1647,n544,n1641,n1644,n1646,n1648,n1643,n402,n400] (by decide +kernel)
def n1651 := cc 9 [w0,w1,w2,w3,w4,w217,w5] [97,179,389,459,524] [n545,n1642,n403,n1650,n401] (by decide +kernel)
def n1652 := cc 6 [w69,w647,w0,w2,w3] [538,662,669] [] (by decide +kernel)
def n1653 := cc 7 [w647,w0,w2,w3,w68,w13] [121,180,538,662] [n1652] (by decide +kernel)
def n1654 := cc 6 [w69,w0,w1,w648,w3] [517,536,669] [] (by decide +kernel)
def n1655 := cc 7 [w0,w1,w648,w3,w68,w13] [121,517,536,662] [n1654] (by decide +kernel)
def n1656 := cc 6 [w69,w649,w0,w1,w3] [397,512,539,662] [] (by decide +kernel)
def n1657 := cc 7 [w649,w0,w1,w3,w68,w13] [121,206,539,662] [n1656] (by decide +kernel)
def n1658 := cc 6 [w69,w650,w0,w1,w2] [662,669,671] [] (by decide +kernel)
def n1659 := cc 7 [w650,w0,w1,w2,w68,w13] [121,180,293,662] [n1658] (by decide +kernel)
def n1660 := cc 6 [w651,w413,w1,w2,w3] [396,537,662,664] [] (by decide +kernel)
def n1661 := cc 7 [w413,w1,w2,w3,w68,w125] [83,121,180,537] [n1660] (by decide +kernel)
def n1662 := cc 6 [w413,w652,w1,w2,w3] [396,537,662,664] [] (by decide +kernel)
def n1663 := cc 7 [w69,w413,w0,w1,w2,w3] [389,512,517,535,662,669] [n1652,n1656,n1658,n1654,n1662] (by decide +kernel)
def n1664 := cc 8 [w413,w0,w1,w2,w3,w68,w13] [121,180,206,389,517,535,662] [n1663,n1653,n1657,n1659,n1661,n1633,n1637,n1655] (by decide +kernel)
def n1665 := cc 7 [w69,w0,w1,w2,w3,w125] [420,452,512,564,664,671] [] (by decide +kernel)
def n1666 := cc 7 [w651,w0,w1,w2,w3,w13] [420,452,564,664,671] [n1660] (by decide +kernel)
def n1667 := cc 8 [w0,w1,w2,w3,w68,w13,w125] [206,420,564,671,675] [n1665,n1666,n1661,n1643] (by decide +kernel)
def n1668 := cc 7 [w0,w1,w2,w3,w653,w13] [121,180,581,664] [] (by decide +kernel)
def n1669 := cc 7 [w521,w69,w0,w1,w2,w3] [512,517,581,664,669] [] (by decide +kernel)
def n1670 := cc 8 [w521,w0,w1,w2,w3,w68,w13] [83,121,180,206,517,581] [n1669,n1668] (by decide +kernel)
def n1671 := cc 7 [w69,w220,w0,w1,w2,w3] [83,452,512,601,662,671] [] (by decide +kernel)
def n1672 := cc 8 [w220,w0,w1,w2,w3,w68,w13] [452,601,662,675] [n1638,n1671,n1644,n1634] (by decide +kernel)
def n1673 := cc 6 [w0,w1,w2,w644,w3,w640,w13] [180,255] [] (by decide +kernel)
def n1674 := cc 6 [w69,w0,w1,w2,w644,w3] [180,402,512,551,662] [] (by decide +kernel)
def n1675 := cc 7 [w0,w1,w2,w644,w3,w68,w13] [206,551,662,671] [n1674,n1673,n1635,n1645] (by decide +kernel)
def n1676 := cc 5 [w655,w654,w0,w1,w3] [180,678,685] [] (by decide +kernel)
def n1677 := cc 6 [w654,w0,w1,w3,w68] [206,671,685] [n1676] (by decide +kernel)
def n1678 := cc 6 [w656,w0,w1,w414,w3] [403,512,671] [] (by decide +kernel)
def n1679 := cc 7 [w0,w1,w414,w3,w68,w44] [206,552,671] [n1678,n1677] (by decide +kernel)
def n1680 := cc 6 [w0,w1,w414,w657,w3] [180,403,512] [] (by decide +kernel)
def n1681 := cc 7 [w69,w0,w1,w414,w2,w3] [401,512,550,662,669] [n1674,n1680] (by decide +kernel)
def n1682 := cc 8 [w0,w1,w414,w2,w3,w68,w13] [121,206,550,662] [n1681,n1636,n1679,n1646,n1675,n1648] (by decide +kernel)
def n1683 := cc 7 [w69,w0,w1,w2,w3,w44] [427,445,574,671] [] (by decide +kernel)
def n1684 := cc 7 [w656,w0,w1,w2,w3,w13] [18,83,427,671] [n1678] (by decide +kernel)
def n1685 := cc 8 [w0,w1,w2,w3,w68,w13,w44] [83,427,574,671] [n1683,n1684,n1679] (by decide +kernel)
def n1686 := cc 6 [w47,w0,w1,w3,w659] [206,512,517,593] [] (by decide +kernel)
def n1687 := cc 7 [w0,w1,w2,w3,w659,w13] [206,589,675] [n1686] (by decide +kernel)
def n1688 := cc 7 [w658,w47,w0,w1,w3,w68] [206,593,671] [n1686,n1677] (by decide +kernel)
def n1689 := cc 7 [w658,w69,w0,w1,w2,w3] [445,512,589,675] [] (by decide +kernel)
def n1690 := cc 8 [w658,w0,w1,w2,w3,w68,w13] [206,589,675] [n1689,n1688,n1687] (by decide +kernel)
def n1691 := cc 7 [w69,w47,w0,w1,w2,w3] [455,603,662,671] [] (by decide +kernel)
def n1692 := cc 8 [w47,w0,w1,w2,w3,w68,w13] [455,603,662,671] [n1688,n1649,n1691,n1647] (by decide +kernel)
def n1693 := cc 6 [w69,w0,w661,w2,w3] [538,662,669] [] (by decide +kernel)
def n1694 := cc 6 [w69,w0,w1,w662,w3] [517,536,669] [] (by decide +kernel)
def n1695 := cc 6 [w69,w0,w1,w663,w3] [397,512,539,662] [] (by decide +kernel)
def n1696 := cc 6 [w69,w0,w1,w2,w664] [662,669,671] [] (by decide +kernel)
def n1697 := cc 7 [w660,w69,w0,w1,w2,w3] [389,512,517,535,662,669] [n1693,n1695,n1696,n1694] (by decide +kernel)
def n1698 := cc 7 [w69,w0,w652,w1,w2,w3] [420,452,512,564,664,671] [] (by decide +kernel)
def n1699 := cc 7 [w642,w69,w0,w1,w2,w3] [420,452,512,601,662,671] [] (by decide +kernel)
def n1700 := cc 7 [w69,w665,w0,w1,w2,w3] [512,517,581,664,669] [] (by decide +kernel)
def n1701 := cc 6 [w69,w0,w667,w1,w2,w3] [402,551,662,671] [] (by decide +kernel)
def n1702 := cc 6 [w666,w0,w1,w657,w3] [403,512,671] [n1419] (by decide +kernel)
def n1703 := cc 7 [w666,w69,w0,w1,w2,w3] [401,512,550,662,669] [n1702,n1701] (by decide +kernel)
def n1704 := cc 7 [w69,w0,w1,w2,w657,w3] [427,574,664,671] [n1702] (by decide +kernel)
def n1705 := cc 6 [w646,w0,w1,w668,w3] [447,512,517,593] [n1419] (by decide +kernel)
def n1706 := cc 7 [w646,w69,w0,w1,w2,w3] [455,603,662,671] [n1705] (by decide +kernel)
def n1707 := cc 7 [w69,w0,w1,w668,w2,w3] [445,512,589,675] [n1705] (by decide +kernel)
def n1708 := cc 8 [w69,w0,w1,w2,w3] [389,524] [n1706,n1699,n1697,n1703,n482,n546,n166,n1700,n1698,n1707,n1704,n405] (by decide +kernel)
def n1709 := cc 7 [w0,w652,w1,w2,w3,w13] [420,452,564,664,671] [n1662] (by decide +kernel)
def n1710 := cc 7 [w0,w1,w2,w657,w3,w13] [180,427,574,662] [n1680] (by decide +kernel)
def n1711 := cc 8 [w69,w0,w1,w2,w3,w13] [389,524,662,675] [n1669,n1689,n1649,n1638,n1691,n547,n1671,n1663,n1681,n406,n1665,n1683,n1709,n1710] (by decide +kernel)
def n1712 := cc 9 [w0,w1,w2,w3,w68,w13] [389,524] [n1670,n1690,n1708,n1711,n483,n1692,n548,n1672,n167,n1664,n1682,n407,n1667,n1685,n1639,n1650] (by decide +kernel)
def n1713 := cc 10 [w0,w1,w2,w3,w68,w4,w5] [97,184,389,459,524] [n484,n549,n168,n408,n1712,n1640,n1651] (by decide +kernel)
def n1714 := cc 8 [w647,w0,w2,w3,w4,w5,w13] [143,178,671,672,687] [n1653] (by decide +kernel)
def n1715 := cc 8 [w0,w1,w648,w3,w4,w5,w13] [143,178,517,521,687] [n1655] (by decide +kernel)
def n1716 := cc 8 [w0,w1,w2,w648,w3,w4,w5,w13] [143,178,517,521,687] [] (by decide +kernel)
def n1717 := cc 8 [w649,w0,w1,w3,w4,w5,w13] [143,182,231,539,621,662] [n1657] (by decide +kernel)
def n1718 := cc 8 [w650,w0,w1,w2,w4,w5,w13] [143,178,351,662,671,672] [n1659] (by decide +kernel)
def n1719 := cc 7 [w669,w1,w2,w3,w4,w5] [83,143,675,687] [] (by decide +kernel)
def n1720 := cc 8 [w413,w1,w2,w3,w4,w5,w125] [83,90,143,687] [n1719,n1661] (by decide +kernel)
def v642 : Closed T 8 := rotateClosed n982 auto1 auto1ok
def n1721 := cc 9 [w413,w0,w1,w2,w3,w4,w5,w13] [143,178,231,389,459,524,671,672,687] [n1714,n1717,n1718,n1007,n1664,n1720,n982,v642,n1716,n1715] (by decide +kernel)
def n1722 := cc 7 [w358,w0,w134,w1,w2,w3,w4,w5] [144,179,218] [] (by decide +kernel)
def n1723 := cc 8 [w0,w134,w1,w2,w3,w4,w5,w125] [83,90,143,218,231,671,687] [n1722] (by decide +kernel)
def n1724 := cc 8 [w0,w357,w1,w2,w3,w4,w5,w13] [83,90,143,231,517,680,684] [] (by decide +kernel)
def n1725 := cc 8 [w0,w1,w414,w2,w3,w4,w5,w125] [39,55,83,179,218,320,355,483,675] [] (by decide +kernel)
def n1726 := cc 8 [w47,w0,w1,w2,w3,w4,w5,w125] [83,178,320,357,420,606,671,684] [] (by decide +kernel)
def n1727 := cc 7 [w358,w0,w1,w2,w226,w3,w4,w5] [179,218,570,637] [] (by decide +kernel)
def n1728 := cc 8 [w358,w0,w1,w2,w3,w4,w5,w13] [83,90,146,184,351,521,637,671,680] [n1149,n1722,n1335,n1727] (by decide +kernel)
def n1729 := cc 8 [w0,w1,w2,w226,w3,w4,w5,w125] [83,90,218,232,320,356,564,581,636,671] [n1727] (by decide +kernel)
def v643 : Closed T 8 := rotateClosed n994 auto1 auto1ok
def n1730 := cc 9 [w0,w1,w2,w3,w4,w5,w13,w125] [143,231,351,564,666,675] [n994,v643,n1169,n1364,n1726,n1728,n1008,n1720,n1150,n1256,n1723,n1724,n1336,n1725,n1729,n1667] (by decide +kernel)
def n1731 := cc 8 [w0,w1,w2,w670,w3,w4,w5,w13] [83,90,143,182,231,351,517,582] [] (by decide +kernel)
def n1732 := cc 8 [w521,w220,w1,w2,w3,w4,w5] [83,90,143,687] [n1719] (by decide +kernel)
def n1733 := cc 9 [w521,w0,w1,w2,w3,w4,w5,w13] [143,178,182,231,351,581,664,666,671] [n1732,n1338,n1670,n1731,n754,n1043,v414] (by decide +kernel)
def n1734 := cc 8 [w671,w0,w1,w2,w3,w4,w5] [143,179,184,267,452,505] [] (by decide +kernel)
def n1735 := cc 8 [w0,w1,w2,w497,w3,w4,w5] [179,267,269,445,453,506,517,660] [n1258] (by decide +kernel)
def v644 : Closed T 8 := rotateClosed n1083 auto1 auto1ok
def v645 : Closed T 8 := rotateClosed n1571 auto1 auto1ok
def v646 : Closed T 8 := rotateClosed n1502 auto1 auto1ok
def v647 : Closed T 8 := rotateClosed n993 auto1 auto1ok
def n1736 := cc 9 [w220,w0,w1,w2,w3,w4,w5] [143,184,269,389,459,505,601,662,675,676] [n1083,v644,n423,n1170,n1365,n1571,v645,n71,n551,n639,n1151,n1259,n1339,n409,n1502,v646,n993,v647,n1008,n1734,n1735,n754] (by decide +kernel)
def v648 : Closed T 8 := rotateClosed n983 auto1 auto1ok
def n1737 := cc 9 [w220,w0,w1,w2,w3,w4,w5,w13] [97,389,459,675,676,684,687] [n1732,n1672,n1008,n983,v648] (by decide +kernel)
def n1738 := cc 6 [w672,w1,w135,w2,w3,w4,w5] [179] [] (by decide +kernel)
def n1739 := cc 7 [w0,w1,w135,w2,w223,w3,w4,w5] [179,218,267,320,675,676] [n1738] (by decide +kernel)
def n1740 := cc 7 [w221,w0,w1,w135,w2,w3,w4,w5] [179,218,267] [n410] (by decide +kernel)
def n1741 := cc 8 [w0,w1,w135,w2,w3,w4,w5] [143,179,218,267,320,420,483,546] [n1740,n1262,n1739,n411] (by decide +kernel)
def n1742 := cc 7 [w0,w1,w135,w2,w222,w3,w4,w5] [143,179,231] [n1738,n412] (by decide +kernel)
def n1743 := cc 7 [w221,w0,w134,w1,w2,w3,w4,w5] [144,179,218] [] (by decide +kernel)
def n1744 := cc 8 [w0,w134,w1,w135,w2,w3,w4,w5] [143,218,231,267,420,675] [n1743,n415,n1742,n413] (by decide +kernel)
def n1745 := cc 8 [w0,w1,w2,w222,w3,w4,w5] [179,269,427,487,547] [] (by decide +kernel)
def n1746 := cc 7 [w672,w0,w134,w1,w2,w3,w4,w5] [132,143,153] [n1738] (by decide +kernel)
def n1747 := cc 8 [w0,w134,w1,w2,w222,w3,w4,w5] [132,143,231,267,427,445] [n1746,n415,n414,n1742] (by decide +kernel)
def n1748 := cc 9 [w0,w134,w1,w2,w3,w4,w5] [0,143,231,267,351,389,459] [n1298,n1168,n71,n1263,n1744,n417,n1747,n1741,n1745] (by decide +kernel)
def n1749 := cc 8 [w0,w1,w135,w2,w3,w4,w5,w13] [231,420,517,675,676,687] [n418] (by decide +kernel)
def n1750 := cc 8 [w0,w1,w2,w222,w3,w4,w5,w13] [231,339,351,445,500,547,626,662,671] [] (by decide +kernel)
def n1751 := cc 8 [w0,w134,w1,w2,w3,w4,w5,w44] [231,675,687] [] (by decide +kernel)
def v649 : Closed T 8 := rotateClosed n1307 auto1 auto1ok
def v650 : Closed T 8 := rotateClosed n984 auto1 auto1ok
def v651 : Closed T 8 := rotateClosed n1503 auto1 auto1ok
def n1752 := cc 9 [w0,w134,w1,w2,w3,w4,w5,w13] [143,231,389,459,687] [n1298,n1307,v649,n420,n1723,n1751,n984,v650,n1503,v651,n1749,n1750] (by decide +kernel)
def n1753 := cc 9 [w50,w0,w1,w2,w3,w4,w5,w13] [83,351,389,459,650,675,684] [n1298] (by decide +kernel)
def n1754 := cc 8 [w0,w1,w2,w644,w3,w4,w5,w13] [231,351,628,662,675,676] [n1675] (by decide +kernel)
def n1755 := cc 7 [w654,w0,w1,w3,w4,w5] [83,231,675,687] [n1677] (by decide +kernel)
def n1756 := cc 8 [w0,w1,w414,w3,w4,w5,w44] [83,231,552,675] [n1755,n1679] (by decide +kernel)
def v652 : Closed T 8 := rotateClosed n985 auto1 auto1ok
def v653 : Closed T 8 := rotateClosed n1504 auto1 auto1ok
def n1757 := cc 9 [w0,w1,w414,w2,w3,w4,w5,w13] [143,178,231,389,459,687] [n1529,n1682,n1725,n985,v652,n1756,n1504,v653,n1754] (by decide +kernel)
def n1758 := cc 8 [w0,w496,w1,w2,w3,w4,w5,w13] [83,231,675,680] [] (by decide +kernel)
def n1759 := cc 8 [w0,w1,w2,w226,w3,w4,w5,w44] [231,339,357,589,639,675] [] (by decide +kernel)
def v654 : Closed T 8 := rotateClosed n1512 auto1 auto1ok
def n1760 := cc 9 [w0,w1,w2,w3,w4,w5,w13,w44] [231,351,517,574,662,666,675] [n1512,v654,n1530,n1265,n1751,n1758,n1756,n1759,n1685] (by decide +kernel)
def n1761 := cc 8 [w658,w47,w0,w1,w3,w4,w5] [83,231,662,675] [n1688,n1755] (by decide +kernel)
def n1762 := cc 9 [w658,w0,w1,w2,w3,w4,w5,w13] [83,231,351,589,675,677] [n1761,n1690,n1484,n1547,v610] (by decide +kernel)
def n1763 := cc 8 [w0,w481,w1,w2,w3,w4,w5] [146,267,269,604,671,672] [n1266] (by decide +kernel)
def n1764 := cc 8 [w0,w673,w1,w2,w3,w4,w5] [179,267,684] [] (by decide +kernel)
def v655 : Closed T 8 := rotateClosed n1557 auto1 auto1ok
def v656 : Closed T 8 := rotateClosed n1121 auto1 auto1ok
def v657 : Closed T 8 := rotateClosed n986 auto1 auto1ok
def v658 : Closed T 8 := rotateClosed n1511 auto1 auto1ok
def n1765 := cc 9 [w47,w0,w1,w2,w3,w4,w5] [97,231,269,389,459,508,603,671,672,684,687] [n1557,v655,n423,n1168,n72,n640,n1121,v656,n1269,n986,v657,n1511,v658,n1530,n1763,n1764,n1484] (by decide +kernel)
def n1766 := cc 8 [w0,w481,w1,w2,w3,w4,w5,w13] [351,604,662,671,675,676,680] [] (by decide +kernel)
def v659 : Closed T 8 := rotateClosed n987 auto1 auto1ok
def v660 : Closed T 8 := rotateClosed n1505 auto1 auto1ok
def n1767 := cc 9 [w47,w0,w1,w2,w3,w4,w5,w13] [83,143,231,389,459,521,671,684,687] [n1761,n1692,n1726,n987,v659,n1530,n1505,v660,n1766] (by decide +kernel)
def n1768 := cc 8 [w0,w1,w2,w3,w227,w4,w5,w13] [231,351,517,636,662,675,676] [n424] (by decide +kernel)
def n1769 := cc 8 [w0,w1,w2,w3,w674,w4,w5,w13] [184,351,487,662,671] [] (by decide +kernel)
def v661 : Closed T 8 := rotateClosed n988 auto1 auto1ok
def v662 : Closed T 8 := rotateClosed n1506 auto1 auto1ok
def n1770 := cc 9 [w0,w1,w2,w226,w3,w4,w5,w13] [182,231,351,524,607,662,675,677] [n552,n426,n1729,n1759,n988,v661,n1506,v662,n1768,n1769] (by decide +kernel)
def n1771 := cc 9 [w675,w0,w1,w2,w3,w4,w5,w13] [83,351,524,607,675,687] [] (by decide +kernel)
def v663 : Closed T 9 := rotateClosed n1084 auto1 auto1ok
def v664 : Closed T 9 := rotateClosed n1308 auto1 auto1ok
def v665 : Closed T 9 := rotateClosed n1558 auto1 auto1ok
def v666 : Closed T 9 := rotateClosed n1572 auto1 auto1ok
def v667 : Closed T 9 := rotateClosed n1122 auto1 auto1ok
def v668 : Closed T 9 := rotateClosed n1294 auto1 auto1ok
def v669 : Closed T 9 := rotateClosed n995 auto1 auto1ok
def v670 : Closed T 9 := rotateClosed n1513 auto1 auto1ok
def n1772 := cc 10 [w0,w1,w2,w3,w4,w5,w13] [97,184,269,389,459,524,607] [n1733,n1300,n1753,n1762,n1771,n1084,v663,n1308,v664,n1558,v665,n486,n1171,n1366,n1572,v666,n1765,n1767,n73,n553,n641,n1122,v667,n1736,n1737,n21,n170,n582,n1721,n1154,n1270,n1294,v668,n1748,n1752,n1342,n1757,n427,n1770,n1712,n995,v669,n1513,v670,n1730,n1760,n1019,n1533,n991,v409,n1509,v607] (by decide +kernel)
def n1773 := cc 8 [w676,w0,w1,w2,w3,w4,w5] [90,97,179,431,577] [] (by decide +kernel)
def n1774 := cc 9 [w0,w417,w1,w2,w3,w4,w5] [184,389,483,524,671,675] [n1085,n1003,n1773,n1514,n429,n754,n1000] (by decide +kernel)
def n1775 := cc 8 [w677,w0,w1,w2,w3,w4,w5] [179,448,512,597] [] (by decide +kernel)
def n1776 := cc 9 [w0,w1,w2,w229,w3,w4,w5] [97,184,389,524,672] [n1559,n1521,n555,n1775,n996,n429,n1484,n428,n1518] (by decide +kernel)
def n1777 := cc 9 [w0,w1,w2,w3,w4,w5,w13] [53,83,143,231,351,389,459,662] [n1529,n1007,n431,n754,n1484,n998,v386,n1516,v582] (by decide +kernel)
def n1778 := cc 9 [w70,w71,w0,w1,w2,w3] [389,459,524] [n488,n556,n173,n432,n1708] (by decide +kernel)
def n1779 := cc 10 [w70,w0,w1,w2,w3,w4,w5] [97,184,389,459,524] [n1086,n1560,n1778,n489,n557,n174,n433,n1002,n1520,n999,n1517,n1774,n1776,n1777] (by decide +kernel)
def v671 : Closed T 10 := rotateClosed n1087 auto1 auto1ok
def v672 : Closed T 10 := rotateClosed n1309 auto1 auto1ok
def v673 : Closed T 10 := rotateClosed n1561 auto1 auto1ok
def v674 : Closed T 10 := rotateClosed n1625 auto1 auto1ok
def v675 : Closed T 10 := rotateClosed n1779 auto1 auto1ok
def v676 : Closed T 10 := rotateClosed n1630 auto1 auto1ok
def v677 : Closed T 10 := rotateClosed n1573 auto1 auto1ok
def v678 : Closed T 10 := rotateClosed n1313 auto1 auto1ok
def v679 : Closed T 10 := rotateClosed n1123 auto1 auto1ok
def v680 : Closed T 10 := rotateClosed n745 auto1 auto1ok
def v681 : Closed T 10 := rotateClosed n1295 auto1 auto1ok
def v682 : Closed T 10 := rotateClosed n1444 auto1 auto1ok
def v683 : Closed T 10 := rotateClosed n1604 auto1 auto1ok
def v684 : Closed T 10 := rotateClosed n1028 auto1 auto1ok
def v685 : Closed T 10 := rotateClosed n1296 auto1 auto1ok
def v686 : Closed T 10 := rotateClosed n1542 auto1 auto1ok
def v687 : Closed T 10 := rotateClosed n1623 auto1 auto1ok
def n1780 := cc 11 [w0,w1,w2,w3,w4,w5] [] [n1087,v671,n1309,v672,n1561,v673,n1625,v674,n1779,v675,n604,n1274,n1351,n1630,v676,n490,n1172,n1367,n1573,v677,n26,n1173,n1275,n1313,v678,n74,n558,n642,n1123,v679,n22,n175,n583,n745,v680,n1155,n1271,n1295,v681,n23,n1343,n1444,v682,n434,n1158,n1604,v683,n599,n1272,n1349,n1713,n1028,v684,n1296,v685,n1542,v686,n1623,v687,n1772] (by decide +kernel)
theorem independentlyEnumeratedBound : Lower true R T 12 :=
  fromClosed n1780 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 5, 4), (0xcccccccccccccccc, 11, 9), (0xf0f0f0f0f0f0f0f0, 5, 1), (0xff00ff00ff00ff00, 11, 3), (0xffff0000ffff0000, 17, 1), (0xffffffff00000000, 33, 1)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide +kernel)
end B51

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xfeeefeeafeeae8a0
theorem fullBound : Lower true fullRoots fullWord 12 := by
  intro p bank h hit
  have hlow := B51.independentlyEnumeratedBound p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276807840)
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
  unfold PEqualNP.Outside.L_meta_46966.Model.Repr at out
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

def mono : List Gate := [⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [14, 17]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 18⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 12) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_46966

open PEqualNP.Outside.L_meta_46966 in
theorem PEqualNP.Outside.L_meta_46966 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact solve fullBound
