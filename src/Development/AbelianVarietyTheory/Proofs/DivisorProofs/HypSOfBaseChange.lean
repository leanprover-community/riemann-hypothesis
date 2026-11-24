module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZeroStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SymDescentAlgClosed

theorem hypS_of_baseChange : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A : PolAV (Sp K)) (B : PolAV (Sp Ω)) (b : B.A.left ⟶ A.A.left), IsGrpPullback B.A A.A (spMap j) b → LBIso B.L (A.L.pull b) → (letI := B.isAb.comm; GlobalTheory.ZH.HypS B.A B.L) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro K Ω _ _ _ _ j A B b h hb hS
  letI := B.isAb.comm
  letI := A.isAb.comm
  obtain ⟨w, wd, hw, hwd, hs, hp, ha⟩ := hS
  obtain ⟨w₀, -, e⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h w hw
  obtain ⟨wd₀, -, ed⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h wd hwd
  exact GlobalTheory.SymLevelDescent.hypS_descend j A.isAb h A.isLB B.isLB hb e ed hw hwd hs hp ha

end GlobalTheory.SymDescentAlgClosed
