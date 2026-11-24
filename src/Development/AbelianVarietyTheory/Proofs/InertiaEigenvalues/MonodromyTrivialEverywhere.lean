module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.GoodRowMono

theorem separable_prod_teich {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {f : (ZMod g)[X]} (hf : Squarefree f) :
    (((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)).prod).Separable := by
  have hnd : ((Formalism.CyclotomicNorms.rootsBar f).map t).Nodup :=
    (nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))).map (GlobalTheory.TameLabels.teich_injective t ht)
  have e : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)) =
      ((Formalism.CyclotomicNorms.rootsBar f).map t).map (fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [e]
  have hs : ((((Formalism.CyclotomicNorms.rootsBar f).map t).map fun a => X - C a).prod).Splits :=
    Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _
  refine (nodup_roots_iff_of_splits (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero hs).1 ?_
  rw [roots_multiset_prod_X_sub_C]
  exact hnd

variable (D : D7)

variable {D}

theorem separable_fixed {σ : D.what₂.FT} {π : D.naut.CG D.R.r} (hg : D.nd.goodRow σ)
    (hlab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v)))
    (k : Fin 2) (v : D.nd.PlG k) :
    (D.naut.inePol (D.naut.locG π (D.naut.plGw k v)) (D.ntypes.tg k v)).Separable := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locG π (D.naut.plGw k v)) := by
    rw [← hlab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]
  rw [D.ntypes.inertiaCharpoly_type k v _ hfull, ← hlab]
  exact separable_prod_teich _ (D.ntypes.teichC_inj k) ((hg k).1.2.1 v)

end GlobalTheory.GoodRowMono
