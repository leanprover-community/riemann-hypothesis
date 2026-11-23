module

public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

def UnramifiedAtLevelPrimes (A : AtTTied u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v (x : 𝓞 D.host.E), A.res v x = 0 →
    (((D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) ≤
      D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
        (x : D.host.E)))

theorem not_dvd_prod_of_not_dvd {ι : Type} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, ¬ (D.mem u).A.T ∣ f i) :
    ¬ (D.mem u).A.T ∣ ∏ i ∈ s, f i := by
  have hT : Nat.Prime (D.mem u).A.T := (D.mem u).A.2
  intro hd
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hT.prime f).mp hd
  exact h i hi hdi

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
