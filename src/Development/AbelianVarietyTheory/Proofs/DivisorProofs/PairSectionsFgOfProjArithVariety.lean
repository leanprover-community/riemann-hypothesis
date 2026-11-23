module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.PairFG

theorem exists_hom {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    (M : HermLB p) (hM : P.Rep a b M) :
    ∃ φ : M.B.Sec →+ X.functionField, φ.range = P.H a b := by
  obtain ⟨ρ, hρ, hu, -⟩ := hM
  obtain ⟨e, he⟩ := RepDict.exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  obtain ⟨c₀, h₀⟩ := hcov M.isLB (genericPoint X)
  have hρ₀ := (ρ c₀).ne_zero
  let φ : M.B.Sec →+ X.functionField :=
    { toFun := e
      map_zero' := by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he 0 c₀ h₀, zero_mul]
        exact map_zero _
      map_add' := fun u v => by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]
        exact map_add _ _ _ }
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨φ, le_antisymm ?_ fun f hf => ?_⟩
  · rintro _ ⟨u, rfl⟩ x i j hi hj
    obtain ⟨c, hc⟩ := hcov M.isLB x
    change RegAt x (P.loc a b (e u) i j)
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · obtain ⟨u, hu'⟩ := RepDict.exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    exact ⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩

theorem h_fg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  intro k _ X _ p D hX P a b
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨φ, hφ⟩ := exists_hom P a b M hM
  have := GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety k X p D hX M.B M.isLB
  rw [← hφ, AddMonoidHom.range_eq_map]
  obtain ⟨S, hS, hfin⟩ := AddGroup.fg_iff.mp this
  apply (AddSubgroup.fg_iff _).mpr
  refine ⟨(φ : M.B.Sec → X.functionField) '' S, ?_, hfin.image φ⟩
  rw [← AddMonoidHom.map_closure, hS]

end GlobalTheory.HSNef.PairFG
