module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolFormNabla

theorem cupSquare_eps {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : GlobalTheory.AbDual.CupSquare (epsDP R) (GlobalTheory.DeRham.epsRed R) A := by
  obtain ⟨C, _, φ, j, hφ, hic, -⟩ := exists_const A
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  exact GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys GlobalTheory.abelianDeRham.1 GlobalTheory.abelianDualCrystal.2
    (isDPNilpotent_squareZero _) su rfl hC gC hic.1 (liftMor (epsDP R) hic)

end GlobalTheory.PolFormNabla
