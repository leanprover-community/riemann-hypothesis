module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenKernelKilledNearPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

theorem exists_open_kerKilled_locus : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G), (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen, s.IsGen) → x ^ d = 1) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → Set.range g.base ⊆ (U : Set S') := by
  intro d S' _ G _ _ P hG hP h1 h2 hs
  refine ⟨sSup {V | GlobalTheory.KerKilledLocus.KerKilledOn d G P V}, ?_, ?_⟩
  · intro V hV
    refine GlobalTheory.T.kernelKilledOverOpen_of_local d S' G P V ?_
    intro p hp
    obtain ⟨W, hW, hpW⟩ := (TopologicalSpace.Opens.mem_sSup).1 (hV hp)
    exact ⟨W, hpW, hW⟩
  · intro T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hu hamp hker
    rintro _ ⟨t, rfl⟩
    obtain ⟨V, hV, hK⟩ := GlobalTheory.T.exists_open_kernel_killed_near_point d S' G P hG hP h1 h2 hs T g A' φ φ₂ P' hpb hsq hP' hiso hu hamp hker t
    exact (TopologicalSpace.Opens.mem_sSup).2 ⟨V, hK, hV⟩

end GlobalTheory.KerKilledLocus
