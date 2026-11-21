import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

def primesAP (m a : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])


end Formalism.HermitianLattices.Ext.SupplyAP
