module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocMemTransfer

theorem mem_locU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ y : GAf L n, TrivOutside {v} y → F.j y ∈ locU n w := by
  intro L _ _ _ n F v w hw y hy
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  refine Subgroup.mem_inf.2 ⟨F.fin y, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
  ext s t
  rw [F.loc y u s t]
  have h := hy (u.under (𝓞 (maximalRealSubfield L))) (by simpa using hu)
  have h0 : compAt L (u.under (𝓞 (maximalRealSubfield L)))
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) s t - (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = 0 := by
    have hst := congrFun (congrFun h s) t
    rw [Matrix.map_apply] at hst
    rw [map_sub, hst]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h1 := (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (GlobalTheory.UnramDict.kappa_tmul F)
    (u.under (𝓞 (maximalRealSubfield L))) _).1 h0 u rfl
  rw [map_sub] at h1
  change F.κ _ u - F.κ _ u = 0 at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp
  rfl

end GlobalTheory.LocMemTransfer

end
