module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.derivative_of_product_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | exact GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv <;> assumption)
