set -euo pipefail

if ! (cargo -v > /dev/null); then
  echo "Cargo is not installed."
  exit 1
fi

echo "Installing compiler binary..."

cargo install mosaic-lang

if [[ "$OSTYPE" == "linux-gnu"* ]]; then
  MODULES_PATH="$HOME/.msc/modules"
elif [[ "$OSTYPE" == "darwin"* ]]; then
  MODULES_PATH="$HOME/Library/Application Support/Mosaic/Modules"
else
  echo "Unsupported OS $OSTYPE"

  exit 1
fi

if ! (git -v > /dev/null); then
  echo "Git is not installed."
  exit 1
fi

mkdir -p "$MODULES_PATH"

cd "$MODULES_PATH"

rm -rf "$MODULES_PATH/core" "$MODULES_PATH/std" "$MODULES_PATH/mosaic"

git clone https://github.com/ljpprojects/mosaic

# Basically copy tests/std and test/core into devstd and devcore

cd mosaic
git checkout nightly

mv tests/std ..
mv tests/core ..

cd ..
rm -r mosaic

ls
