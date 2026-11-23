module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
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
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  exact @GlobalTheory.Mum.cube_step
