#! /bin/bash

rm -r ~/Library/Application\ Support/Mosaic/Modules/std
rm -r ~/Library/Application\ Support/Mosaic/Modules/core

cp -r tests/std ~/Library/Application\ Support/Mosaic/Modules
cp -r tests/core ~/Library/Application\ Support/Mosaic/Modules
