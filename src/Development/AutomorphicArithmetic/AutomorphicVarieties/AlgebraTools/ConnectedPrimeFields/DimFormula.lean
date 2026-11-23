module

public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
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
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.dimFormula :
    ∀ {R : Type} [CommRing R] [IsDomain R], HasBase R → IsNoetherianRing R ∧ ReciprocityTheory.CA.DimFormula R := by
  intro R _ _ h
  obtain ⟨A, _, _, i, hA, hinj, hf⟩ := h
  let : Algebra A R := i.toAlgebra
  have : Module.Finite A R := hf
  have : IsDomain A := hA.dom
  have : IsIntegrallyClosed A := hA.normal
  have : IsNoetherianRing A := hA.cm.1
  have hinj' : Function.Injective (algebraMap A R) := hinj
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing A R
  refine ⟨this, fun q _ => ?_⟩
  set p := q.comap (algebraMap A R) with hp
  have : q.LiesOver p := ⟨rfl⟩
  have h1 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  have h2 : q.height ≤ p.height := by
    have e1 := PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum R)
    have e2 := PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum A)
    simp only at e1 e2
    rw [e1, e2]
    exact Order.height_le_height_apply_of_strictMono
      (fun P : PrimeSpectrum R => (⟨P.asIdeal.comap (algebraMap A R),
        inferInstance⟩ : PrimeSpectrum A))
      (fun P Q hPQ => Ideal.IsIntegral.comap_lt_comap (R := A)
        (show P.asIdeal < Q.asIdeal from hPQ)) _
  rw [le_antisymm h2 h1,
    ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) q,
    hA.cm.height_add_ringKrullDim_quotient,
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj']
