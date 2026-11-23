module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjUnit

theorem ideleConj_mem_unitIdl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro E _ _ _ y hy
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have key : ∀ z : Neutral.B1.Ideles E, z ∈ GlobalTheory.Mem.Chr.unitIdl E → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E z : AdeleRing (𝓞 E) E)).2 w) ≤ 1 := by
    intro z hz w
    have hz' : ∀ v : HeightOneSpectrum (𝓞 E), ((z : AdeleRing (𝓞 E) E)).2 v ∈ v.adicCompletionIntegers E :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := v)).mpr (hz v).le
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo E E w (hz' _)
  intro w
  have h1 := key y hy w
  have h2 := key y⁻¹ (inv_mem hy) w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y : AdeleRing (𝓞 E) E)).2 w *
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y⁻¹ : AdeleRing (𝓞 E) E)).2 w = 1 := by
    rw [map_inv]
    exact congrArg (fun a : AdeleRing (𝓞 E) E => a.2 w) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y).mul_inv
  have e' := congrArg Valued.v e
  rw [map_mul, map_one] at e'
  exact eq_one_of_one_le_mul_left h1 h2 e'.ge

end GlobalTheory.ConjUnit
