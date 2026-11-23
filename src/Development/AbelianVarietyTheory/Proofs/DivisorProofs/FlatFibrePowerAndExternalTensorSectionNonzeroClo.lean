module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

namespace GlobalTheory.BoxNonzeroClosed

theorem flat_powObj {S : Scheme.{0}} (G : Over S) [Flat G.hom] : ∀ n : ℕ, Flat (Out.powObj G n).hom
  | 0 => inferInstanceAs (Flat (𝟙 S))
  | n + 1 => by
    have := flat_powObj G n
    exact inferInstanceAs (Flat (pullback.fst G.hom (Out.powObj G n).hom ≫ G.hom))

theorem flat_pow {S : Scheme.{0}} (G : Over S) [Flat G.hom] (N : ℕ) : Flat (pow G N).hom := by
  have := flat_powObj G N
  let e : pow G N ≅ Out.powObj G N :=
    (productIsProduct (fun _ : Fin N => G)).conePointUniqueUpToIso (Out.powIsLimit G N)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

theorem main : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec),
    NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  rintro V _ _ G _ L θ ⟨g, hg, hθ⟩ N
  refine ⟨flat_pow G N, ?_⟩
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.BoxSection.exists_point (fun k => Pi.π (fun _ : Fin N => G) k)
    (productIsProduct (fun _ : Fin N => G)) _ (fun _ => g) (fun _ => hg)
  exact ⟨y, hy, GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec L (pr G N) (fun _ => θ) y
    fun i => (hy' i).symm ▸ hθ⟩

end GlobalTheory.BoxNonzeroClosed
