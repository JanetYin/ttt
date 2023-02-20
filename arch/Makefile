all: readme.html

%.html: %.md
	pandoc $< > $@

clean:
	rm -f *.html
