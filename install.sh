set -euo pipefail

if ! (cargo -v > /dev/null); then
  echo "Cargo is not installed."
  exit 1
fi

echo "Which branch do you want to use?"

select branch in "Stable" "Nightly"; do
    case $branch in
        Nightly ) cargo install --version latest mosaic-lang; break;;
        Stable ) cargo install mosaic-lang; break;;
    esac
done

if [[ "$OSTYPE" == "linux-gnu"* ]]; then
  MODULES_PATH="$HOME/.msc/modules"
elif [[ "$OSTYPE" == "darwin"* ]]; then
  MODULES_PATH="$HOME/Library/Application\ Support/Mosaic/Modules"
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

rm -r "$MODULES_PATH/mosaic-core" "$MODULES_PATH/mosaic-std" "$MODULES_PATH/core" "$MODULES_PATH/std" || true

git clone https://github.com/ljp-projects/mosaic-std.git
git clone https://github.com/ljp-projects/mosaic-core.git

mv mosaic-core core
mv mosaic-std std

ls