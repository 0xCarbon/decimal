module github.com/0xCarbon/decimal/benchmarks/incumbents

go 1.27.1

require (
	github.com/0xCarbon/decimal v0.0.0
	github.com/cockroachdb/apd/v3 v3.2.3
	github.com/ericlagergren/decimal v0.0.0-20240411145413-00de7ca16731
	github.com/govalues/decimal v0.1.36
	github.com/shopspring/decimal v1.6.0
)

replace github.com/0xCarbon/decimal => ../..
