module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (σ : Representation LL G V)

end Jumps

def blockJumps (t : ℕ) : Multiset ℤ := (Finset.Ico (0 : ℤ) (t : ℤ)).val

def SplitsAs {k Γ : Type} [Field k] [Group Γ] {n r t : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) k)
    (P : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → Γ → k) : Prop :=
  ∃ e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)), ∀ (g : Γ) (u : Fin n → k),
    e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ c g * (e u).2 c)

section HidaSetting

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def BlockSplit (π : N.X i) : Prop :=
  SplitsAs (mapM (toK N i) (rO N i r π)) (mapM (toK N i) (rhoO N i ρ π))
    (fun (c : Fin R.t) g => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i))

def HidaSetting (π : N.X i) : Prop :=
  GoodR N i r ∧ π ∈ N.Z i ∧
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
    BlockSplit N i r ρ π

variable {N} (L : LocTheory) (nbr : Br.NBr N)

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

end
