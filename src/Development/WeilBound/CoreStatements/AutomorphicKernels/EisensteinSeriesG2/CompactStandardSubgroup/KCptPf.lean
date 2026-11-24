module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
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

@[expose] public section

noncomputable section

namespace SiegelEisensteinSeries.BRoad

open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem isCompact_intHat : IsCompact (intHat F E : Set (AE F E)) := by
  have hZ : (⊤ : Submodule ℤ (𝓞 E)).FG := Module.Finite.fg_top
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have : CompactSpace (GlobalTheory.ThK.Dbl.St.intF F) := isCompact_iff_compactSpace.1 GlobalTheory.ThK.Dbl.St.isCompact_intF
  let f : (Fin m → GlobalTheory.ThK.Dbl.St.intF F) →+ AE F E :=
    AddMonoidHom.mk' (fun (a : Fin m → GlobalTheory.ThK.Dbl.St.intF F) => ∑ j, (a j : AF F) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E)) fun (a b : Fin m → GlobalTheory.ThK.Dbl.St.intF F) => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : ((a + b) j : AF F) = a j + b j := rfl
      rw [this, add_smul]
  have hf : Continuous f := by
    change Continuous fun a : Fin m → GlobalTheory.ThK.Dbl.St.intF F => ∑ j, (a j : AF F) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E)
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun a : Fin m → GlobalTheory.ThK.Dbl.St.intF F => (a j : AF F) :=
      Continuous.subtype_val (continuous_apply j)
    exact h1.fun_smul continuous_const
  have e : intHat F E = f.range := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨a, ha, ha', o, rfl⟩
      have ho : o ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ho
      refine ⟨fun j => c j • ⟨a, ha, ha'⟩, ?_⟩
      change ∑ j, (c j • a) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E) =
        a • inclR (F := F) (AF F) (((∑ j, c j • s j : 𝓞 E)) : E)
      have hc : (((∑ j, c j • s j : 𝓞 E)) : E) = ∑ j, c j • ((s j : 𝓞 E) : E) := by push_cast; rfl

      rw [hc, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    · rintro _ ⟨a, rfl⟩
      change (∑ j, (a j : AF F) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E)) ∈ intHat F E
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨a j, (a j).2.1, (a j).2.2, s j, rfl⟩
  rw [e, AddMonoidHom.coe_range]
  exact isCompact_range hf

end SiegelEisensteinSeries.BRoad
