import Taeyoung.Catalogue.Rows

/-! Kernel-checked cardinality and status-count audits for the generated list. -/

namespace Taeyoung.Catalogue

open Taeyoung

def countStatus (s : CatalogueStatus) : ℕ :=
  (rows.filter fun row => row.status = s).length

theorem row_count : rows.length = 117 := by decide
theorem positive_count : countStatus .positive = 73 := by decide
theorem negative_count : countStatus .negative = 23 := by decide
theorem open_count : countStatus .open = 21 := by decide

end Taeyoung.Catalogue
