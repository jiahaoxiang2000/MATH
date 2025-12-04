// Shared dependencies and commands for all chapters
// Import this file in each chapter to access common packages and utilities

// Import theorem environment package
#import "@preview/theorion:0.3.2": *

// Import diagram/drawing package
#import "@preview/cetz:0.4.1"

// Custom color functions
#let redt(content) = text(fill: rgb("#DC143C"), content)
#let bluet(content) = text(fill: rgb("#1E90FF"), content)
#let greent(content) = text(fill: rgb("#32CD32"), content)

// Custom mathematical operators
#let rad = math.op("rad")
