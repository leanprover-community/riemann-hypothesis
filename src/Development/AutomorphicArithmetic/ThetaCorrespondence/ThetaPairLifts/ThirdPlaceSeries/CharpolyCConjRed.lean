module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Triple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
section Wild
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end Wild
section Row
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)
theorem charpoly_cConj_eq_charpoly_inv_of_mem_ine (hD : FrobDense D) {n : ℕ} {π : D.naut.CG n} (hπ : D.naut.csd π) {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l} {r : GalE D →* GL (Fin n) (Qbar l)}
    {ρ : GalE D →* GL (Fin n) (Formalism.CyclotomicNorms.Fbar l)} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (hρ : IsReduction D red r ρ)
    {v : PlE D.host} (hv : v ∉ placesOver D.host.E l) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver A v)
    {s : GalE D} (hs : s ∈ Ine (F := D.host.E) A) :
    ((ρ (cConj Y s) : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly =
      ((ρ s⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly := by
  have h := _root_.GlobalTheory.TripleResidual.charpoly_cConj_eq_charpoly_cyc_zpow_smul_inv Y hD hπ hr s
  rw [cyc_eq_one_of_mem_Ine hv hA hs, Units.val_one, one_zpow, one_smul] at h
  obtain ⟨p, p1, p2⟩ := hρ.2.2 (cConj Y s)
  obtain ⟨q, q1, q2⟩ := hρ.2.2 s⁻¹
  rw [← p2, ← q2, Polynomial.map_injective _ Subtype.val_injective (p1.trans (h.trans q1.symm))]
end Row
section Triples
end Triples
end GlobalTheory.TripleResidual
end
end
