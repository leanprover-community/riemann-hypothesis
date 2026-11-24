module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetricStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem canon_isBiRig : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  intro R _ _ _ hCN Q G _ _ P hC
  obtain ⟨hP, D', F, A', G', i1, i2, U', oA, oG, inc, pr, hsemi, hlin, hinc, hpr, hip, hpi, hiso⟩ := hC
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  have hros := GlobalTheory.T.linearUniformisation_rosatiAdjoint_star R hCN D' F.O F.o A' G' U' oA oG hsemi hlin
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hf : IsMonHom (inc ≫ oG.act F.f) := by have := oG.hom F.f; infer_instance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.mumfordBundle_pullback_homPair_trivial_axes (Sp R) G G' U'.LG.L hL inc (inc ≫ oG.act F.f) hinc hf P hP hiso
  exact ⟨hP, h1, h2, GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric (Sp R) G G' U'.LG.L hL F.O oG hros F.e F.f inc hinc hie F.alg.2.1 P hP hiso⟩

end GlobalTheory.Mum
