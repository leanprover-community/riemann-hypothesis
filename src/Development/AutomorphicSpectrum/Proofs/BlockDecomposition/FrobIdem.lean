module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FrobLc

variable {l : ℕ} [Fact l.Prime]

theorem frob_idem (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) : A.frob e = e := by
  change e ^ l = e
  have h := IsIdempotentElem.pow_succ_eq (l - 1) he
  rwa [Nat.sub_add_cancel (Fact.out : l.Prime).one_lt.le] at h

theorem lcRes_id (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) :
    lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (RingHom.id A.Ug))) f = f := by
  have e : Spec.map (CommRingCat.ofHom (RingHom.id A.Ug)) = 𝟙 (SU A) := by
    change Spec.map (𝟙 (CommRingCat.of A.Ug)) = 𝟙 _
    exact Spec.map_id _
  rw [e]
  ext x
  rfl

theorem phi_lcA (hN : LcNat) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU A) (ZMod (l ^ n))) : A.phi n (lcA A n f) = lcA A n f := by
  have h := (hN l H A hA n).1 A hA A.frob A.pdOk_frob (RingHom.id A.Ug)
    (fun e he => by rw [frob_idem A e he]; rfl) f
  rw [lcRes_id] at h
  exact h

section Gen
universe w w' u v u' v'
variable {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
  {σ : R →+* R'} {ρ : R' →+* R'}

theorem cls_congr {K : CrystallineSemistableComparison.Cx.{w} R} {k : ℕ} {x y : K.X k} (h : x = y) (hx : K.d k x = 0) (hy : K.d k y = 0) :
    K.cls x hx = K.cls y hy := by
  subst h; rfl

theorem pull_fix (m : Mor F F' σ) (p : Mor F' F' ρ) (j : ℕ) (h : ∀ z, p.pullC j (m.pullC j z) = m.pullC j z)
    (c : CH.H F j) : p.pull j (m.pull j c) = m.pull j c := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact cls_congr (h z) _ _
end Gen

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem phi_lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ)
    (z : Cn (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L j) :
    (phiMor M.P n).pullC j ((lcM hN H r M n).pullC j z) = (lcM hN H r M n).pullC j z := by
  funext s
  exact phi_lcA hN H _ (s.obj (Fin.last j)).1.property n _

theorem fPhi : CrystallineSemistableComparison.E.FPhi := fun hN l _ H r K M n j x =>
  pull_fix (lcM hN H r M n) (phiMor M.P n) j (phi_lcM hN H r M n j) ((pts H r M (𝟭 _) n).et 0 j x)

end GlobalTheory.CompanionTheory.FrobLc
