module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

open GroundTheory.Global.SemiLocal in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.splitOfDec :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.SplitOfDec := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ v h w
  haveI : Module.Finite K M := Module.Finite.of_restrictScalars_finite ℚ K M
  haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w.1
  have hv : IsPlaceOver A v := fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, w.2.over]
    exact hA (algebraMap (𝓞 K) (𝓞 M) x)
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (F := K) (K := M) (L := M) hv hA hA
    (fun s hs => ⟨{ s.toRingEquiv with commutes' := h A hv s hs }, AlgEquiv.ext fun _ => rfl⟩)
  have hr := finrank_eq_ramificationIdx_mul_inertiaDeg M v w.1
  rw [he, hf] at hr
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hr).2
