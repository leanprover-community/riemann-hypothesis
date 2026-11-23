module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Affine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.KeyGenAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PermMatrixMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem pKey (hT : PTransfer) : PKey := by
  intro hCh hEv hAff L _ _ hC k hk π hπ n r hn1 hr1 F hFinv hFcoc z hz
  haveI := (pIndex L (n + r) π hπ).1
  haveI := (pIndex L n π hπ).1
  have hSK := pStabK L π hπ.ne_zero n r hn1
  refine keyGen hT hSK.1 hSK.2 (fun c => pGqStab L π hπ n r hn1 c) k F hFinv hFcoc ?_ z hz
  intro c hc H hH w hw
  have hlow : ∃ i : Fin r, ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))
      (Fin.natAdd n i) ⟨0, by omega⟩ ∉ Ideal.span {π} := by
    by_contra hne
    push_neg at hne
    obtain ⟨c', hc'⟩ := pLow L π hπ n r hn1 c hne
    exact hc c' hc'
  have h := pStabVan hCh hEv hAff L hC k hk π hπ n r hn1 hr1 c hlow F hFinv hFcoc H hH w hw
  simpa only [map_mul, mul_assoc] using h

end PositivityTheory.KB.AffineStabilizerVanishing

end
