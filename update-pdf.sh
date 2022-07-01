ls *.md | sed 's/\.md//g' | xargs -I % pandoc %.md -o %.pdf
