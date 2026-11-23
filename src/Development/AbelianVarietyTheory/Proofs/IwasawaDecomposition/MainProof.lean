module

public import Formalism.UnipotentAdelicQuotients.WeylLatDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMemIffStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualBasesColProdStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasisStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpandStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem mainProof : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hrow hzero φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le_of_rowLen (hzero s N le_rfl)
  have hν : ∀ s, ν (e s) = fun r : Fin N => (nu s).rowLen r := fun s => funext fun r => (hrow s r).symm
  choose ι hι hdec b g c d Nc hNc h1 h2 h3 h4 h5 using fun s => GlobalTheory.T.dual_bases_colProd_alt GlobalTheory.T.columnMinorProducts_fock_reproducing_identity N (nu s) (hY s)
  rw [GlobalTheory.T.integral_minors_iff_basis_alt p Lt N nu hY ι b c d h1 h2 φ]
  have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) = fun y =>
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) :=
    funext fun y => GlobalTheory.T.phi_DeX_expand_alt p Lt T e N nu hY ι b g c h1 h3 φ y
  rw [hfun, GlobalTheory.T.comb_mem_iff_alt p Lt T e he N ν ι b g Nc hNc h4 (fun s => by rw [hν s]; exact h5 s)]

end GlobalTheory.WeylLatDualProof
