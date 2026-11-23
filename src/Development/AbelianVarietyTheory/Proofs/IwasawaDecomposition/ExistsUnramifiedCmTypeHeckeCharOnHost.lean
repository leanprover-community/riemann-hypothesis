module

public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.ChiPsiExist


open Classical in
theorem exists_chiPsi : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : HChar H.E, IsChiPsi H χ := by
  intro R H
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => -1) ∅ (fun _ => 1)
      (fun w hw => absurd hw (Finset.notMem_empty w))
      (by
        intro ζ hζ
        rw [Finset.prod_empty, mul_one]
        exact UpperTheory.Mu.prod_emb_zpow H (Equiv.refl _) hζ _)
  exact ⟨χ, hu, fun v => hunr v (Finset.notMem_empty v) (fun w hw => absurd hw (Finset.notMem_empty w)), ht, hi⟩

end GlobalTheory.Mem.ChiPsiExist
