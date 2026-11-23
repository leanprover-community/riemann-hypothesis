module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpenStatement
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

namespace GlobalTheory.KerKilledNear

theorem kerKilledOn_near : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, ∃ V : S'.Opens, g.base t ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hd hamp hker t
  obtain ⟨Ua, hUa, hUa'⟩ := GlobalTheory.T.diagonal_restriction_relAmple_locus_open S' G P hA hP
  obtain ⟨Ud, hUd, hUd'⟩ := GlobalTheory.T.natCast_unit_locus_open S' d
  have hsa : g.base t ∈ Ua := hUa' T g A' φ φ₂ P' hpb hsq hP' hiso hamp ⟨t, rfl⟩
  have hsd : g.base t ∈ Ud := hUd' T g hd ⟨t, rfl⟩
  exact GlobalTheory.T.kernelKilledOverOpen_near_of_fibre d S' G P hA hP hg₁ hg₂ hsym (Ua ⊓ Ud) (fun V hV => hUa V (hV.trans inf_le_left))
    (hUd _ inf_le_right) (g.base t) ⟨hsa, hsd⟩
    (GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat d S' G P hA hP hg₁ hg₂ hsym T g A' φ φ₂ P' hpb hsq hP' hiso hd hker t)

end GlobalTheory.KerKilledNear
