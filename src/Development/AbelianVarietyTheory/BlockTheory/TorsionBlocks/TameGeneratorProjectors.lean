module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.CyclotomicNorms.StatementI

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def OnW (σ : D.what₂.FT) : Prop := ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' {a} ha := by show ‖-a‖ ≤ 1; rwa [norm_neg]

def IsReduction {a l : ℕ} [Fact l.Prime] (red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l)
    (r : GalE D →* GL (Fin a) (Qbar l)) (ρ : GalE D →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsOpen (ρ.ker : Set (GalE D)) ∧ IsSSRep ρ ∧ ∀ g, ∃ p : (Zbar l)[X],
    p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
    p.map red = ((ρ g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def toFb (k : Fin 2) (c : (ZMod (D.host.g k))ˣ) : Fb (D.host.g k) (D.host.g_prime k) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k))

end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
