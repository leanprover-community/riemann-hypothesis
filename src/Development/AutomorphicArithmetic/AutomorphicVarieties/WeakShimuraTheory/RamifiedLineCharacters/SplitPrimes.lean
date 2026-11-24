module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.splitPrimes :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) →
      Set.Infinite {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
  intro Ω _ _ _ H hH
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  set U : Subgroup (G ℚ Ω) := N.toOpenSubgroup.toSubgroup with hUdef
  haveI : U.Normal := N.isNormal'
  have hUo : IsOpen (U : Set (G ℚ Ω)) := N.isOpen'
  have hUH : U ≤ H := fun x hx => hN hx
  intro hfin
  set M : ℕ := ∏ q ∈ hfin.toFinset, q with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro q hq
    exact ((hfin.mem_toFinset.mp hq).1).ne_zero
  obtain ⟨w, A, p, σ, -, hp, hpM, -, hpw, hnorm, -, hpl, hIne, hfr, hσ⟩ :=
    UpperTheory.V.Loc.v00 (F := ℚ) U hUo 1 ∅ M hM0
  have hσU : σ ∈ U := by simpa using hσ
  have hDecU : Dec (F := ℚ) A ≤ U :=
    UpperTheory.V.Kum.decGen ℚ Ω A w σ U hpl (by rw [hnorm]; exact hfr) hUo hIne hσU
  have hAp : A.valuation (p : Ω) < 1 := by
    have := (hpl (p : 𝓞 ℚ)).mpr hpw
    simpa using this
  have hmem : p ∈ {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
    refine ⟨hp, fun A' hA' y hy => ?_⟩
    obtain ⟨u, hu, -⟩ := ((UpperTheory.V.Chr.placesQ Ω).2.2) p A' A hp hA' hAp
    have h1 : u⁻¹ * y * u ∈ U := hDecU (hu y hy)
    have h2 : y ∈ U := by
      have := (inferInstance : U.Normal).conj_mem _ h1 u
      simpa [mul_assoc] using this
    exact hUH h2
  exact hpM (hM ▸ Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hmem))
