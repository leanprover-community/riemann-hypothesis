import Development.AutomorphicArithmetic.QuadraticCharacters.MemRealCyclotomicSubgroup
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

open Formalism.HC Formalism.FrobeniusOrbits

noncomputable section

namespace HostParam.Seam

def IsRes (E : AbField) {M : ℕ} (r : (ZMod M)ˣ →* E.Gal) : Prop :=
  ∀ (a : ℕ) (h : a.Coprime E.N) (h' : a.Coprime M), r (ZMod.unitOfCoprime a h') = E.res (ZMod.unitOfCoprime a h)

structure FrameIso (C : Core) (φ : Frame) where
  iso : C.E.Gal ≃* φ.GG
  e_eq : φ.e = C.e
  ps_eq : ∀ g, φ.psC (iso g) = C.psG g
  ch_eq : ∀ g, φ.chC (iso g) = C.chG g
  conj_eq : iso C.E.conj = φ.cc
  iota_eq : iso C.iota = φ.iod
  A0_eq_image : ∀ g, g ∈ C.A0 ↔ ∃ s ∈ φ.A0, iso g = φ.tau1 s
  h_eq : ∀ (u : (ZMod C.E.N)ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod C.E.N).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (iso (C.E.res u)).2 = hcl φ.e v

structure Comparison₂ (C : Core) {φ : Frame} (H : HostRaw φ) extends FrameIso C φ where
  d_eq : H.d = C.d
  art_res : ∀ (a : ℕ) (h : a.Coprime C.E.N) (h' : a.Coprime H.condN),
    H.art (ZMod.unitOfCoprime a h') = iso (C.E.res (ZMod.unitOfCoprime a h))

def Comparison₂.resMap {C : Core} {φ : Frame} {H : HostRaw φ} (t : Comparison₂ C H) : (ZMod H.condN)ˣ →* C.E.Gal :=
  t.iso.symm.toMonoidHom.comp H.art



def FrameIso.pull {C : Core} {φ : Frame} (F : FrameIso C φ) (θ : φ.Char) : C.E.Gal →* ℂˣ := θ.comp F.iso.toMonoidHom

structure AdmQ (C : Core) (q : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_split : SplitsIn C.d q
  q_inertia : Nat.card (C.E.inertia q) ≤ 2

structure admitted (C : Core) (q QS : ℕ) : Prop extends AdmQ C q where
  QS_pos : 0 < QS
  QS_coprime : Nat.Coprime QS (q * C.d)
  QS_split : ∀ l : ℕ, l.Prime → l ∣ QS → SplitsIn C.d l
  cond_dvd : C.E.conductor ∣ QS * q * C.d

def smallPart (C : Core) (q : ℕ) : ℕ := ordCompl[q] (ordCompl[C.d] C.E.conductor)

def abField {φ : Frame} (H : HostRaw φ) : AbField := ⟨H.condN, H.condN_pos, H.art.ker⟩

def ofP (ψ : PChar) : PrimChar := ⟨ψ.N, ψ.χ⟩

def toP (κ : PrimChar) (h : 0 < κ.1) (hp : κ.2.IsPrimitive) : PChar := @PChar.mk κ.1 ⟨h.ne'⟩ κ.2 hp


theorem ofP_fst_pos (ψ : PChar) : 0 < (ofP ψ).1 := Nat.pos_of_ne_zero (NeZero.ne ψ.N)

theorem ofP_snd_isPrimitive (ψ : PChar) : (ofP ψ).2.IsPrimitive := ψ.prim

theorem toPrimitive_ofPrimitive (ψ : PChar) : toP (ofP ψ) (ofP_fst_pos ψ) (ofP_snd_isPrimitive ψ) = ψ := rfl







structure TypeTie (T : HostType) (T' : HType) (κ : HConst) : Prop where
  eps_eq : T'.eps = T.eps
  kept_eq : ofP '' (T'.KEPT : Set PChar) = T.kept
  psK_eq : T'.psK.map ofP = T.psK
  P0_eq : T'.P0 = T.P0
  t_eq : T'.t = T.t
  Ct_eq : T'.Ct = T.Ct
  o_le : T.o ≤ κ.oB
  rB_eq : κ.rB = T.rrBound
  c_eq : κ.c = T.cA
  C_eq : κ.C = T.CB

def rescale (T : HostType) (T' : HType) (X : ℝ) : ℝ := X ^ ((T'.J : ℝ) / T.J)


def withA0 (C : Core) (U : Subgroup C.E.Gal) (h1 : U ≤ C.A)
    (h2 : ∀ u : (ZMod C.E.N)ˣ, C.E.res u ∈ U → C.hG (C.E.res u) = 1 → C.E.res u = 1) : Core :=
  { C with A0 := U, base_exponent_le_a := h1, A0_inf_stabilizer_trivial := h2 }

structure RecordRows {φ : Frame} (H : HostRaw φ) (b : ℕ) : Prop where
  QS_exact : H.Exact
  QS_le : H.QS ≤ φ.ord ^ 2
  o_pow : φ.o ^ 64 ≤ 2 ^ φ.e
  q_ne_three : H.q ≠ 3
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(H.d : ℤ)) p = 1
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → 4 * l ≤ b

def InWin (eps x : ℝ) (n : ℕ) : Prop := x ^ (2 + 8 * eps) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps)

structure PreRows (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostRaw φ) (rr rr' : ℕ) : Prop where
  one_le_X : 1 ≤ X
  x_ge : X ^ ((1 : ℝ) / T.J) ≤ x
  x_le : x ≤ X
  ha5 : φ.TorsionIndexBounded κ.oB
  ha6 : H.OddPrimesSplitBelow (T.z X)
  ha7 : H.SmallPrimeSizeBounds T.SM (T.z X)
  ha8 : H.DiscriminantConductorSizes (T.z' X)
  ha9 : H.ModulusSizeBounds (T.z X)
  ha12 : H.PrimePairSizeCondition (T.z X) κ.rB rr rr'


end HostParam.Seam

end
